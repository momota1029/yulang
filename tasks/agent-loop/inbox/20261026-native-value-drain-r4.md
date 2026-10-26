# Native Value drain r4 — frozen primary author handoff

Author: `/root`. Original baseline: `82b8fb669c5b51c6c99771cd2208c9730ebc85c3`.
Frozen at 2026-10-26T12:42:17.477089+00:00. Fresh nonauthor review required; no self-certification.

## Claim and original application

The full construction, native crosswalk, data retention and original OPEN gates
are in `notes/theory/2026-10-26-native-value-drain.md`. The module constructs the
actual prepare/admit/enqueue control history from the original computed structural
Value children. Its final root `context_value_pipeline` starts from the actual
outer Context/Value computation and actual preflight, constructs a shared drain
prefix, and derives every child's diagnosed ReturnReady occurrence in any matching
quiescent continuation. The middle state and matching port/control history are
conclusions. Original full source semantics, authenticated global committed native
readback and conflict-free diagnostics remain separate required owners.

Every raw child, complete admitted key, original current occurrence and separately
selected processing relation is retained. Admission and enqueue are distinct;
old native queue contents are unrestricted. Ghost task names encode full raw task
payloads and do not claim native allocation. The preflight explicitly handles
commit re-arming and the actual replay-operation wait/queued/consumed guards.

No solver, source syntax, expected result, root configuration, default toolchain,
scheduling index or production feature changed. The original parent remains
`SourceProblem.InferenceSoundness`; this handoff does not close it.

## Review correction before acceptance

The fresh reviewer found a documentation imprecision: Control.nextWork and the
serial/issued/returned occurrence history are ghost proof annotations attached
to actual enqueue/return events, not stored Rust fields. The note now states
this explicitly. Its prior SHA256 was 5d871d81e6c23489d0ae0e403b3a8fe7b79d47064505c870340801cfee58d8b7. No Lean source or theorem changed,
and no repeated compiler check was needed. The earlier freeze and handoff are
retained under value-drain-r4/pre-review-*.

## Frozen hashes

| Artifact | SHA-256 |
| --- | --- |
| NativeValueDrain.lean | `826fa025241835aad606434b3d0fee2406b694d72ca1dbf03a618f3e61d1b095` |
| Construction note | `0f1ea3a6d0c57f3ac3f2a4d4ca552f0fa01fe45354132c52f401434f55304949` |
| Complete originating census | `edcc8b2417987283fdfdf2a1f588f9ccc189cdc8aba88706c082309ab778d2cf` |
| Origin audit source | `1801a3ad2f44be55088cdc00b096f449ed1e3b45d1a840028b31b6b6fc84fec0` |

## Resource bounds and retained failures

Assignment: 2,700 wall seconds, at most18 focused Lean calls. Used 12/18.
Each invocation was confined to the owned isolated project/cache and TMPDIR,
one CPU and `-j1 -M1024`; helper bound115 seconds, outer bound119 seconds,
sampled wrapper/Lake/Lean aggregate RSS ceiling1280MiB. Exact commands, versions,
exit status, hashes and process evidence are below. Total measured checker wall
seconds: 105.284381; maximum sampled aggregate
RSS: 1169854464 bytes.

Calls01–03 repaired ordinary Lean elaboration issues (reserved field/argument,
indexed constructor binders, map composition, Run.nil disambiguation and a
rewritten equality). Call04 checked the first enqueue-only construction and05
its full census. Source review then found the material native preflight boundary:
that construction applies only after preparation, not to an arbitrary raw active
frame. Those superseded artifacts and all failure logs remain retained; neither
is counted as final original native correspondence. Calls06–08 construct actual
preparation, repair its dependent record equalities, prove repeat preparation is
complete, and exercise real commit/re-preparation. The separately accepted outer
Value module was then pinned by exact published bytes. Calls09–10 exposed only a
new theorem's existential type/binder syntax and a deprecated simp lemma. Call11
checks every final authored root with no warning/error. Call12 audits every
originating declaration, including private/generated constants, and has no
warning/error. Its complete output reaches EOF; the independent parser validates
unique balanced blocks, every full type and every transitive axiom report.

No checker process or descendant remains active. Source/note/handoff writes stop
at this freeze; primary retains Git and later integration ownership.

## Complete origin inventory

```json
{
  "declarations": 204,
  "theorems": 85,
  "roots": 34,
  "all_axioms": {
    "none": 106,
    "propext": 81,
    "Quot.sound, propext": 14,
    "Classical.choice, Quot.sound, propext": 3
  },
  "theorem_axioms": {
    "none": 25,
    "propext": 43,
    "Quot.sound, propext": 14,
    "Classical.choice, Quot.sound, propext": 3
  },
  "root_axioms": {
    "propext": 17,
    "Quot.sound, propext": 14,
    "Classical.choice, Quot.sound, propext": 3
  },
  "log_sha256": "edcc8b2417987283fdfdf2a1f588f9ccc189cdc8aba88706c082309ab778d2cf",
  "replacement_characters": 0,
  "omitted_type_terms": 0
}
```

All 85 theorem constants appear with complete printed types and axiom
reports below. The 34 authored roots are a subset, not an alternate
inventory. All 204 originating declarations were audited; no
project axiom, sorryAx, unsafe/native bypass or omitted type term is accepted.
Standard dependencies are only propext, Classical.choice and Quot.sound.

## Exact input manifest

The later dependency addition is separately timestamped and pinned to its public
commit and ACCEPT review. All original inputs remain byte-identical.

```json
{
  "baseline": "82b8fb669c5b51c6c99771cd2208c9730ebc85c3",
  "started_utc": "2026-10-26T12:12:31.293485+00:00",
  "wall_budget_seconds": 2700,
  "check_budget": 18,
  "inputs": {
    "AGENTS.md": "ce73e9754ba9fd00bd2c4395d322ce77730a26aafb586d51de8ad169d7f8d48f",
    "AGENTS.pre-sprint.md": "34b8b8169696dcc6a0899204226914d250ddecf6782d14be670b7b2d5352c562",
    ".agents/skills/yulang-lean-proofs/SKILL.md": "05346b8c6e3d9cdd1715da1774bb26cf7bce313233782240b3493bd9ee8754a7",
    ".agents/skills/yulang-lean-proofs/references/sources.md": "cb3f1009e80f0f9f7a1bf2575b4144e002a72f21e474c66b441e1f626a1e4d4a",
    ".agents/skills/yulang-lean-proofs/references/execution.md": "a1d8c47550e8925220623e0401410556d92719aff5590c459ac4c2e88306800b",
    ".agents/skills/yulang-lean-proofs/scripts/check_lean.py": "a4f10b70297cbf4d8b5bc0c7526bc29783eaf417f1f70e53eeea341d1150dde6",
    "rules/goal-driven-sprints.md": "e50f5d4f79814c87af56e7dc34ddb6ab968abb523826c72ecdc40a8920397c0a",
    "crates/yu-solver/src/lib.rs": "ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07",
    "crates/yu-solver/src/candidate_context.rs": "57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e",
    "notes/theory/lean/YulangClosure/NativeValuePorts.lean": "f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa",
    "notes/theory/lean/YulangClosure/NativeDrainOwnership.lean": "d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18",
    "notes/theory/2026-10-26-native-value-ports.md": "4f39788f4dee30f5f413b0b373965ea583892b7d07e5b95de63ccb93f2819b5b",
    "notes/theory/2026-10-26-native-drain-ownership.md": "1e725751031322517c213662b0e0f1cf7b6e96bef656e2a6e45a40d67aee24e6",
    "notes/theory/lean/YulangClosure/NativeValueStructure.lean": "81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc",
    "notes/theory/2026-10-26-native-value-structure-r5.md": "ab9d3d278f6635285bb5888671d3f7ade9dfa50c56b39c30b49f74f203e35bc7",
    "tasks/agent-loop/inbox/20261026-native-value-structure-review-r5.md": "860c43c47d470607d8f59ac7fb5e155048abc1eb80fceda560f293f027d39633"
  },
  "project": {
    "notes/theory/lean/.lake/R22Audit.lean": "ff63bb4a3a557699c7a88beca4d26008f7f71039eaa066a6324c4f1ae309182c",
    "notes/theory/lean/.lake/call-entry-spine-r1-check.lean": "3a51fe2832d496516071f0e677be40433a35cf046bad1d28c1a44fbbe891ac5e",
    "notes/theory/lean/.lake/call-entry-spine-r2-check.lean": "4b2722280ad703f81ce172f7426a3cc694083459f74bf14121b1cfe2d3da45ed",
    "notes/theory/lean/.lake/call-entry-spine-r3-check.lean": "5e54e62da9aeff020127b20112ccbd6e669e3cb7ff5ae03adbfffd317d2b4389",
    "notes/theory/lean/.lake/call-progress-obstruction-r3-check.lean": "c249ae83737295e01aab6c5f6397f1367c10f907ba25f22c6ebcbed0b269905d",
    "notes/theory/lean/.lake/call-unwind-r2-check.lean": "77a685433f4815977207ee32a5ba9cf49d707a993e43a29c169cb12954f0df0b",
    "notes/theory/lean/AuditExecutionProofs.lean": "aa16f7e520fc56b6694e04d42e81a6f58c0ffe64b4db30c432fb2bd77692052f",
    "notes/theory/lean/AuditInferenceProofs.lean": "b6c5e8dac8fa9d0f01f558cb82d9eb492d1112f7382038b3ff1ff62d3ff085e1",
    "notes/theory/lean/AuditProofAdvancement.lean": "95a10406b14ad9e073e17857b012c9a3c2940bac84c32e21a5fca268562a52dd",
    "notes/theory/lean/YulangClosure.lean": "3c38da4bb2e017249fa973e0ee28f243d44ba6d52b6f173ac617b605f1fce9e8",
    "notes/theory/lean/YulangClosure/BirthLevelSCC.lean": "2c76b82d4dc85a4bf4c122731ba014b07df4c863ad679e9a795a57e6546243f0",
    "notes/theory/lean/YulangClosure/BoundaryQueryClosure.lean": "7dad22c1b94e404be5dc4aaa51203e8d3882fd4c61006eb8b0c5f6f87a30f727",
    "notes/theory/lean/YulangClosure/CallCaptureResponse.lean": "a310f3da1091a2dd7ed1d751aea67c44aefe06ce89fc9bb16cc0d19b530eb1c6",
    "notes/theory/lean/YulangClosure/CallCaptureTyping.lean": "906e8204aa155efd3f4e45d9c2a2a9fbe010858206ef3dd0acfd3d0d607a0de9",
    "notes/theory/lean/YulangClosure/CallContextTyping.lean": "09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125",
    "notes/theory/lean/YulangClosure/CallDeclaredLiteralResponse.lean": "f9c7f3b8b0c2ad0552df531a6a13ad1fb4863340bb0ea837319bf144a2bae255",
    "notes/theory/lean/YulangClosure/CallEntrySpine.lean": "6c6bd7b4c912e86196434465a94a1ada02fe1d28cc8c0e5343b247a2dd7961b6",
    "notes/theory/lean/YulangClosure/CallEntrySpineComposition.lean": "a296a5ae738cb3ca8f88a6009495e0fe84a2a394976aafeb4630d6cdd25a11bf",
    "notes/theory/lean/YulangClosure/CallEntrySpineRepair.lean": "ad4a2e1b49b13dc71b77b079b80b0c6c6355327915a4be343276b9b9497f7d89",
    "notes/theory/lean/YulangClosure/CallEntryTyping.lean": "21850ac899060ade9f9db5139b20e5e1779b4f18b67d6d1127501827ec146ba2",
    "notes/theory/lean/YulangClosure/CallEntryTypingRepair.lean": "f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39",
    "notes/theory/lean/YulangClosure/CallEnvironmentRealization.lean": "8b9e4c38224f103557c5f6a036c6d4d06ba7799264947f4843fa7029195f66b6",
    "notes/theory/lean/YulangClosure/CallFailureUnwind.lean": "2d7422bc4c83310a1a1d0a2bcaa5528bb6a8801520c42db2f2ada6b12224b89c",
    "notes/theory/lean/YulangClosure/CallFiniteTyping.lean": "555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588",
    "notes/theory/lean/YulangClosure/CallLiteralResponse.lean": "62cffcd2bcf5ce879c3c7b75ff6908b19470a27e5ca73e5973ec1affbeaac3fb",
    "notes/theory/lean/YulangClosure/CallNativeLiteralResponse.lean": "7b0c27ba851f982d3e13fa3e27c258fe907a56585a92123af14f9ad4d765d2cd",
    "notes/theory/lean/YulangClosure/CallPeelingTyping.lean": "f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44",
    "notes/theory/lean/YulangClosure/CallPrefixTyping.lean": "95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc",
    "notes/theory/lean/YulangClosure/CallProgressObstruction.lean": "8dc8b1b72c952dc45c431fb965a438b700dc86902a68b8d77a3de0b7d47858b7",
    "notes/theory/lean/YulangClosure/CallRequestBoundary.lean": "28ffc2943c18d324c35dacf18b4dd70921d4cc462ffd6ffdce989475ef46cce6",
    "notes/theory/lean/YulangClosure/CallRequestBoundaryComposition.lean": "fed00f06cdbf2a5bdc1b3c18957acc33c7b281e890f277ca5bd1d20ece53ee76",
    "notes/theory/lean/YulangClosure/CallRequestUnwind.lean": "e4835bd2c2487b14d658b02373e0507ea6c201b81a1fb81d396b0f05a1850fc9",
    "notes/theory/lean/YulangClosure/CallResponseCancellation.lean": "ab9083bab971acd4e72cb8db95d567b309a240e1773b3fc4544fa6968ffe9488",
    "notes/theory/lean/YulangClosure/CallStepTyping.lean": "4b3b40ae3c295666470c1cda73ac38f0abdc62ea86626be58f10249092d3c3ab",
    "notes/theory/lean/YulangClosure/CallStepTypingRepair.lean": "2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586",
    "notes/theory/lean/YulangClosure/CallTerminalTyping.lean": "319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d",
    "notes/theory/lean/YulangClosure/CallUnwindTyping.lean": "57afc331d735c7b9680c8b1391ced1f86b72a0ab10ca37e9f620cf0388af1cc1",
    "notes/theory/lean/YulangClosure/CallUnwindTypingRepair.lean": "1eaea1938f6ee2341352afcc597847fc2ade5b8ce8d3be84dda19926fe217cc3",
    "notes/theory/lean/YulangClosure/CallViewedForceReachability.lean": "ce6e45da496ceb3f5d7e1150f57ebdf5f62dd0495ee3a8deb1b61035b39cee8c",
    "notes/theory/lean/YulangClosure/CallViewedForceStuck.lean": "71164cef48ca86866ef4aae9661ea2e9388e9741062e159a97f3c26b42614ae9",
    "notes/theory/lean/YulangClosure/Contracts.lean": "2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e",
    "notes/theory/lean/YulangClosure/ControlComposition.lean": "4e8e4cb4fdf106bbffa11e21cd9f7030bda1f296f14e1a554560ea802f02dc5e",
    "notes/theory/lean/YulangClosure/ControlSyntax.lean": "1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0",
    "notes/theory/lean/YulangClosure/ControlTyping.lean": "e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f",
    "notes/theory/lean/YulangClosure/CoreComposition.lean": "1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c",
    "notes/theory/lean/YulangClosure/CoreControlBridge.lean": "30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a",
    "notes/theory/lean/YulangClosure/CoreExecution.lean": "86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e",
    "notes/theory/lean/YulangClosure/CoreSubstitution.lean": "ae1dfd4947d9e87c05dfa893b93067175d860ed3b5da000d61257d7789208b55",
    "notes/theory/lean/YulangClosure/CoreSyntax.lean": "c5a25cb7d935159b62f377b7fa88b3e92e4cdf429118d566e53f7859f6ea5375",
    "notes/theory/lean/YulangClosure/DeclSubst.lean": "f1463d4dceeab7251b2a65508b23a7ef4ab3a575b2792793be04a858e9191258",
    "notes/theory/lean/YulangClosure/FiniteGuardDecision.lean": "a9924ab2c8d96a173c886ddfbb2580a7719fbf08064d9f85d0644784778de9fa",
    "notes/theory/lean/YulangClosure/ForceAdmin.lean": "620994e5e7383c267a19d5bea93f35d8d82d2db76a03893449bd821250669c97",
    "notes/theory/lean/YulangClosure/ForceCompletion.lean": "6baeb9a786e916d0f7b60bd4d5c8286657da2adba4acdab36f2e45e0921aeb22",
    "notes/theory/lean/YulangClosure/GraphContinuationExtension.lean": "cae749a64bb641131aa6fdc19a71fe0c635dbe007433556f3dc9efe4388105ec",
    "notes/theory/lean/YulangClosure/GraphExtensionTransport.lean": "a41bbdb417d3a5f9c1784b690520d5a973d1178c5a1ab47b6b5b80cdd629dac1",
    "notes/theory/lean/YulangClosure/GuardedValueGraph.lean": "4d2c3b17d0ab8d12606c875638426167ce596492167cecf042eb222436229f55",
    "notes/theory/lean/YulangClosure/HandlerGraphCorrespondence.lean": "94a6c2d24045bf9959121f4b31efea2f0630abc53c5bb776ab356d3ff108f964",
    "notes/theory/lean/YulangClosure/HandlerGraphEmbedding.lean": "36b616d809554feb585f32203fa72c1a084c7136beb4141a46d3a27a5145f656",
    "notes/theory/lean/YulangClosure/HandlerGraphInteraction.lean": "a5094f70dc2ec2843a431cfb24f0111166fbc9172b7e6df08d0d8c800a8ce018",
    "notes/theory/lean/YulangClosure/HandlerGraphRecAllocation.lean": "5563163a5fe2741dc4cb1968329e5ec417a170099448978b653dc487cd136dfd",
    "notes/theory/lean/YulangClosure/HandlerGraphRecInteraction.lean": "dc1f89a1e1b8b0b4a9e2e95fdcc47334b1b7578a8fef3f947574678ce8dfdba7",
    "notes/theory/lean/YulangClosure/HandlerGraphRecursiveTrace.lean": "bd07ea464ba42b1073b69b2af0bc5d26c1ca148a58598d6d10973ba54dc29909",
    "notes/theory/lean/YulangClosure/HandlerGraphSafety.lean": "554c5a1a003f27c3b8657d77455aa4f5eda7852338254034e3dd63a6db42a558",
    "notes/theory/lean/YulangClosure/HandlerGraphSyntax.lean": "2a6b3f455e408336290bbe28616d7db8ee928f1b342b4c80f975bbacb419c24c",
    "notes/theory/lean/YulangClosure/HandlerGraphTransport.lean": "a869e61005910dba00cf9cfa57065a45afeac08413974e343d9bcc16821f629d",
    "notes/theory/lean/YulangClosure/HigherOrderEmbedding.lean": "2b773edf831d04cd4319e1fb980865dff0fb9a38f7d64b21f3d228ea2a0e1457",
    "notes/theory/lean/YulangClosure/HigherOrderEntry.lean": "c9cb839ff6b34ed97c5d72f9e020437d32175cf517a5841a3a024764747c213b",
    "notes/theory/lean/YulangClosure/HigherOrderEnvironment.lean": "84a461fdff85e7321cf090ba2bb72a7d90415515a2da1eb15e1287ef0361ab83",
    "notes/theory/lean/YulangClosure/HigherOrderGraphObservation.lean": "8817db7bc5181481745f49696d7b7d2e4dc927a715353ab83bc36f4ed53420cc",
    "notes/theory/lean/YulangClosure/HigherOrderGraphSafety.lean": "de67122c098579b5ba088ff832ef8ca36e233537faf064ab8e36520cf2532533",
    "notes/theory/lean/YulangClosure/HigherOrderGraphSyntax.lean": "2dca03ee408f7f35545c02847d03fae47ab1887c2761c82e8b59cc9ad6001886",
    "notes/theory/lean/YulangClosure/HigherOrderHandlerInteraction.lean": "a0920fc7214055fd213bc66729e865b571698f95bd42ae289c432b6cf5730d3f",
    "notes/theory/lean/YulangClosure/HigherOrderHandlerSafety.lean": "f74c35666d8f4f5ab1af52009c005d5cb0be9958f7f8d64185c31750b2dd38ef",
    "notes/theory/lean/YulangClosure/HigherOrderHandlerSyntax.lean": "4578e2d3c8b06a57937dd652e06eabb8c9271113a7eb3388dc718856d64b249d",
    "notes/theory/lean/YulangClosure/HigherOrderInteraction.lean": "45f2b8c74e2837e503db84aed3c9f55767a32d19e4008546e25a01cef1202875",
    "notes/theory/lean/YulangClosure/HigherOrderRecAllocation.lean": "30a6e1855fb8bb4950ad2bdfad238e000554563cb0d1d4b1ec311e3c0cf4f0dd",
    "notes/theory/lean/YulangClosure/HigherOrderSafety.lean": "16a38dbb649677ed5e6b6371a61228a1724b9e899136eeb2119b755ecab30336",
    "notes/theory/lean/YulangClosure/HigherOrderSubstitution.lean": "19910452c45b20761ec06dc7e15f94c94b95014ff00f3f5296af005b9adf6f30",
    "notes/theory/lean/YulangClosure/HigherOrderSyntax.lean": "ea727d33692bdcbe6b40245b960d01225b556b5334ffab649eea2699930d5972",
    "notes/theory/lean/YulangClosure/InferenceProofs.lean": "dff8f66fb20d1a75cd1ff72ab72babecf30cfb8ad816b5e758c540c1b166afea",
    "notes/theory/lean/YulangClosure/NativeClosureEnvironment.lean": "39aa5cefa078dd423e54f0d9790f9a48e136326742e01f65149f317c907be957",
    "notes/theory/lean/YulangClosure/NativeContextExpansion.lean": "9887bef34e51678cead77eaf84a2f9b47916987ea9cffaad5d4ef74d53de2ea8",
    "notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean": "d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070",
    "notes/theory/lean/YulangClosure/NativeDrainOwnership.lean": "d37edac29dcecc19dd90b91c3095e5385a0657310dcf08d805a8f20672872d18",
    "notes/theory/lean/YulangClosure/NativeExecutionHistory.lean": "44ad2a6d5b9ac0526ea36adc9180e0ed66e3892e48fa39aa40b20999dc7a1da6",
    "notes/theory/lean/YulangClosure/NativeFrameRollback.lean": "274e9a9ac1c43bc81d3b962edb6846dd5e4fa2adb2b645ebd92d6d5f38bd9964",
    "notes/theory/lean/YulangClosure/NativeIntegerArithmetic.lean": "5adb30eb53f64fa4ccad80e83ed78c27f442436f20a8eceb8bc4fb59aac33ad1",
    "notes/theory/lean/YulangClosure/NativeIntegerComparison.lean": "2352602b7047611e9f9722d788ed1acdf9f4960d178c48f6a08b1a7054f93e79",
    "notes/theory/lean/YulangClosure/NativeLiteralReadback.lean": "53a745397fed4b319225541b8e764a32cdc72032ca4e8be48d9d4a23d3901c54",
    "notes/theory/lean/YulangClosure/NativeMergeExpansion.lean": "f14bd35e8f7a6b9f326dadf003797c63f4a48fd0d0c0c9d68891c579560baf6e",
    "notes/theory/lean/YulangClosure/NativeProfileRestriction.lean": "527d89b982b962e423cfaa15ecf76a2d778603102bfc9e8d12b22af2eb1c7fb2",
    "notes/theory/lean/YulangClosure/NativeRecordPlan.lean": "3cf43fdb754748b83a6816791d640752dda491b87f7e2513a27548a950b27d43",
    "notes/theory/lean/YulangClosure/NativeReplayAcknowledgement.lean": "5264c6b6d9904a43ec0b50c3ac0100a05612b724f52a8601e3a93c771f8204df",
    "notes/theory/lean/YulangClosure/NativeReplayCoverage.lean": "e65d925ab5222fd6bbc4bf63e756701aaba1273fff677ceb052d7f66e6450b7e",
    "notes/theory/lean/YulangClosure/NativeReplayCurrent.lean": "fdd7dfa32f944f09b2cfc7440caeff95edcfad1fd5c839094f186d27168d9088",
    "notes/theory/lean/YulangClosure/NativeRowModel.lean": "30016f40295a803df2ed3d9b46efd256d1427400f55bda1810e22a00f89d7780",
    "notes/theory/lean/YulangClosure/NativeRowSaturation.lean": "9f8e2cf43ade40c17a09387d5888833002ee42791eff0d2d608f83d6ca39e974",
    "notes/theory/lean/YulangClosure/NativeTemplateReplay.lean": "cae76713a1756a5d15d13232a094437003931b33b6cc2e5a44ca946d83175d32",
    "notes/theory/lean/YulangClosure/NativeValuePorts.lean": "f49bf12537633c65b4dbdcb4e739df5de5eee76cfb5ad845c8dba50cef4101fa",
    "notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean": "ab37f3739d89dff9e7918fb745f5a308a3e597ab4aaa9e5a172fcacaeddabf0b",
    "notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean": "3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1",
    "notes/theory/lean/YulangClosure/PaperAllocationExecution.lean": "d5cd9f4499ec0c6e67e73a9444634671e43b507368c418b1d9ecec7fd57f0aa4",
    "notes/theory/lean/YulangClosure/PaperCallEntryFormation.lean": "2465c5620b0b66f6029ab294134d9860cd8bf810ac25c5f30763cb709c7da31e",
    "notes/theory/lean/YulangClosure/PaperCombinedExecution.lean": "58661ddec13e1fe4abb6a9b6627597fa824dedbf36f952e56dc15906141314d1",
    "notes/theory/lean/YulangClosure/PaperCoreControl.lean": "71594dfb24af402f7b4835dc54b5383a46106faba959b687295cc0431361530e",
    "notes/theory/lean/YulangClosure/PaperCoreStep.lean": "6357b14217e82421eed87da981cef8e94014dcaea634d746ad0b4bb39bff6144",
    "notes/theory/lean/YulangClosure/PaperEliminationExamples.lean": "d7b412df9bf7cfe47c538b48e1fb6ebfd8fc6c177d484cc3912573608d53071d",
    "notes/theory/lean/YulangClosure/PaperExecutionBinderLaws.lean": "568a9a5a1991bb605d85e9b58f33638fb445b1325516e10eed0f076f72346d7a",
    "notes/theory/lean/YulangClosure/PaperExecutionGraphWeakening.lean": "5fcb0334dfa77c3385f5f460669e36578a01642a54d17e357c072fd012fc73fe",
    "notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean": "d3a10c0891b0518fef7ed6e02c899b996d3ac6de618e07bddde11c89ef616bfe",
    "notes/theory/lean/YulangClosure/PaperExecutionTypingSubstitution.lean": "cb0941ef8842551da53fbf2b14cca181c10849178288de29cef1145f1d575cc7",
    "notes/theory/lean/YulangClosure/PaperExtendedExecution.lean": "a29c5cc15748e8a91338f2a068e94ff7dc58c2a19adad564ba3f5a6fea337ea7",
    "notes/theory/lean/YulangClosure/PaperFreshHeapAllocation.lean": "7cd87b8e5fd43eea0206401de6ed91e817755f3d1ad2c5aeee1caf0dd1732925",
    "notes/theory/lean/YulangClosure/PaperHeapExecution.lean": "46a9e8e76f5745cbaffc40b7bb95ff37064941a84532fa5edc07672ddad3d59f",
    "notes/theory/lean/YulangClosure/PaperHeapObservation.lean": "19b54b87b63cdc4175b1b641ca83d0c1e9454e2439c58a0936bf31fa5bc4725f",
    "notes/theory/lean/YulangClosure/PaperOperationMapperTyping.lean": "175c307e00bea7ba6ec44ff153f50a7d9d943de8bdc3d4dccb02a41bc53dde77",
    "notes/theory/lean/YulangClosure/PaperPerformLetExecution.lean": "2f0026049554cb870158115b4bab8d42f7cbee8b030ee3f84a904763c328cac0",
    "notes/theory/lean/YulangClosure/PaperResumeExecution.lean": "5ab59033b0cea347144c50a5323e4dd6cb59cc6bfbdc0bffd063a4808e741935",
    "notes/theory/lean/YulangClosure/PaperTemplateExecution.lean": "3ead9cf7d0f57d02d5fd8b44da24f133d7859e76dff8ee1d1b17cb233920d792",
    "notes/theory/lean/YulangClosure/PaperTermSubstitution.lean": "d2dde517343a18b03a8fb0fe113b1d0fceeef2751f53792ef39886d8ed5e9c94",
    "notes/theory/lean/YulangClosure/PaperTermSubstitutionAlgebra.lean": "b35a14e1872cec5284a68cb38e9ea6fd0c9dc23cbd6d8017c82a550ec60a379d",
    "notes/theory/lean/YulangClosure/PaperTupleSplitExecution.lean": "7bc13a41a0333d885b91291a7fbb1ef18302a94c79a34f21469dbae19d76f84d",
    "notes/theory/lean/YulangClosure/PaperTypeApplicationPreservation.lean": "60e095545530bc784487a4bfcc1c7acfc1160b3adf8c1c8dc03ab98806154556",
    "notes/theory/lean/YulangClosure/PaperTypeBetaExecution.lean": "0a1834040a0201c0c472f66138f6501094f7138dd3614f2bc4439a8be0cda1c8",
    "notes/theory/lean/YulangClosure/PaperTypeFormation.lean": "29c1a85b4d2588224bf1847f78a7b4d94db095488f3bba4937888a3815f39d13",
    "notes/theory/lean/YulangClosure/PaperTypeSubstitution.lean": "02834720f622642dd4c7a27ea51451deb7386877b091fbccc828a66eaa8e4861",
    "notes/theory/lean/YulangClosure/PaperViewExecution.lean": "e7c6c959d2bcc780ca7198aae09a0368f4d98625001bdfe5b8f8c259c9cb3f85",
    "notes/theory/lean/YulangClosure/PrimitiveOperationInstance.lean": "c3b0f2ad86fd49f9ebcf22c80388b996951ff0704695e18afa546863ddcf8773",
    "notes/theory/lean/YulangClosure/ProofAdvancement.lean": "db2f2f3a548b0b20b15b2435f08a362e903c3e52a035c7eca5580925f08dd598",
    "notes/theory/lean/YulangClosure/RecordBoundaryExecution.lean": "865c4db37b3eed02d8cc376cf07b469c85ef364aeed7914823b207d14730cda2",
    "notes/theory/lean/YulangClosure/RecordBoundaryPreservation.lean": "1bde9224c1b0d568d5cc73d84a5ccc5f1157452c87ea2ff428096c1dbd50d056",
    "notes/theory/lean/YulangClosure/SimpleSubConstraintSoundness.lean": "33709d3978e8071708c10bba23d85b1b025c11dfd988220501acb7c6e3220293",
    "notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean": "a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6",
    "notes/theory/lean/YulangClosure/SimpleSubGeneralizationSoundness.lean": "3f6114e4173d6cade6ad135ed83ad543116e28e87845b0f6a834cb8f727f6246",
    "notes/theory/lean/YulangClosure/SimpleSubGrowingInference.lean": "865b9eb4a64962182a22a9e507b98b1e7ab92ac143e4cbfea0b8570e39bb58ce",
    "notes/theory/lean/YulangClosure/SimpleSubLatticeCertificates.lean": "55533eee35ed7058abd125ac0e01d8f29b8c0534800018d254c1bd9f9c0bb79b",
    "notes/theory/lean/YulangClosure/SimpleSubLatticeDecision.lean": "a9c184512bf6e23d15cc8a3a2ed230652fb168f707155e779be18c562d8e57c9",
    "notes/theory/lean/YulangClosure/SimpleSubLatticeGrowingInference.lean": "1270e3407ddeef881020610b094709ebba07b62a97e54712bcc4b139ef8e78d0",
    "notes/theory/lean/YulangClosure/SimpleSubLatticeInference.lean": "c534c060dfde84f2817fbaa53222f430b59d9b6377cfacedabeca7b9b4b8ffa3",
    "notes/theory/lean/YulangClosure/SimpleSubRegularCompletion.lean": "d7231d0a3695dba7f3102e5fe235d4d26e34cad78870dbdbae9b7633c42787aa",
    "notes/theory/lean/YulangClosure/SimpleSubRegularConstraintSoundness.lean": "1d2266867115fc27afe39dbb80a3ca0e8f75247a2e16b739145137e83999de33",
    "notes/theory/lean/YulangClosure/SimpleSubRegularDecision.lean": "6b6e5e6f1c45140d935e1aa29fba4c1303ae89cd91fd6e1cde0d37387148db8d",
    "notes/theory/lean/YulangClosure/SimpleSubRegularGraphExtension.lean": "0b45d0e6d58701cba9f7df00d2a63897327e357ed3047b36e96d8fb6c49893d8",
    "notes/theory/lean/YulangClosure/SimpleSubRegularPublication.lean": "18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99",
    "notes/theory/lean/YulangClosure/SimpleSubRegularSolutions.lean": "755d267714bd23bcfc17ec37d43d258392567b7d1356afc4897f541ae9855b29",
    "notes/theory/lean/YulangClosure/SimpleSubScopedPublication.lean": "d64e9bffca5d513985237a9ff78dcf3d9e43baae1594edbc93dff4b5410d428f",
    "notes/theory/lean/YulangClosure/SourceFunctionMembership.lean": "8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424",
    "notes/theory/lean/YulangClosure/SourceGeneratedInteraction.lean": "16952fef6ea505cce0d7f8afa6bf39cd3609119626f7857d6beaa88737c5b003",
    "notes/theory/lean/YulangClosure/SourceIdentityLambda.lean": "831b297998509eb261f7a0596792c826c56078661d5a3ab66fc9afd67238d7a4",
    "notes/theory/lean/YulangClosure/SourceIdentityWorld.lean": "6019fd9d57cde50183e016bd0c72de2c6eee72009065d85119fb0348dbcf0168",
    "notes/theory/lean/lake-manifest.json": "058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3",
    "notes/theory/lean/lakefile.toml": "cab85ff9a8a7dc5103fe932739dcea0dfc02e6420b1277565449882c802473bd",
    "notes/theory/lean/lean-toolchain": "ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c",
    "notes/theory/lean/YulangClosure/NativeValueStructure.lean": "81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc"
  },
  "owned_outputs": [
    "notes/theory/lean/YulangClosure/NativeValueDrain.lean",
    "notes/theory/2026-10-26-native-value-drain.md",
    "tasks/agent-loop/inbox/20261026-native-value-drain-r4.md"
  ],
  "dependency_additions": [
    {
      "at_utc": "2026-10-26T12:38:54.320475+00:00",
      "published_commit": "e5d2b7b7a6ec340743668075780e95e8a98c8ef5",
      "paths": {
        "notes/theory/lean/YulangClosure/NativeValueStructure.lean": "81060e17ad37f2e4a47edb7ed2829bea6820438bf3d4db0e4de8d113fd9497fc",
        "notes/theory/2026-10-26-native-value-structure-r5.md": "ab9d3d278f6635285bb5888671d3f7ade9dfa50c56b39c30b49f74f203e35bc7",
        "tasks/agent-loop/inbox/20261026-native-value-structure-review-r5.md": "860c43c47d470607d8f59ac7fb5e155048abc1eb80fceda560f293f027d39633"
      },
      "reason": "Compose the accepted actual outer Context/Value child computation directly with same-history preflight, issuance and return."
    }
  ]
}
```

## Retained check receipts

```json
[
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:14:41.388884+00:00",
    "wall_seconds": 33.9385497780022,
    "exit": 1,
    "peak_aggregate_rss_bytes": 996331520,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "df9cbced1fffd88b9c600233189316dec27d421446decd8f4fc980caacd509aa",
    "log_sha256": "56201fc76d413114b1db409bbe8c24efbf6c98dbb84b5c484bc6301519d5b64a",
    "seen_pids": [
      132847,
      132849,
      132853,
      132857,
      132860,
      132867,
      133139
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:16:24.638119+00:00",
    "wall_seconds": 8.812458682004944,
    "exit": 1,
    "peak_aggregate_rss_bytes": 943828992,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "cd5d9528697d84fdb10f95216eb89e20c54ca535091e656b8df34356b7c62b61",
    "log_sha256": "ed9ab38a447014ad6aadf559f066593693dd9c75c0f8806acfb0d76d803cd112",
    "seen_pids": [
      133497,
      133500,
      133504,
      133508,
      133511,
      133517
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_drive_constructs_common_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_prefix",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_lookup",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.four_ports_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:18:35.356976+00:00",
    "wall_seconds": 2.2323035489971517,
    "exit": 1,
    "peak_aggregate_rss_bytes": 944771072,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "a794a58a1723fe72ebde6f748853ba1c27c0349f1974062091dff1333ab88543",
    "log_sha256": "1acf7877fc2dec41b52cbbe8d2d319247b005cff4a3958635a106e9a629fd8ea",
    "seen_pids": [
      134343,
      134346,
      134350,
      134354,
      134357,
      134364
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_drive_constructs_common_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_prefix",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_lookup",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.four_ports_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:19:14.932792+00:00",
    "wall_seconds": 5.436159853998106,
    "exit": 0,
    "peak_aggregate_rss_bytes": 1158946816,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "2295098a1b738bfc9961405cd90d99985fca93c58cc813f113ddce0c1ba01029",
    "log_sha256": "1d300dac3442b20c823f3bbe59458f97a5c5bb4b15f30a69801e1f98418af18d",
    "seen_pids": [
      134736,
      134738,
      134742,
      134748,
      134751,
      134758,
      134774,
      134779
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--no-cache",
      "env",
      "lean",
      "-j1",
      "-M1024",
      "AuditNativeValueDrain.lean"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:21:06.770410+00:00",
    "wall_seconds": 1.6304844449987286,
    "exit": 0,
    "peak_aggregate_rss_bytes": 1146912768,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "2295098a1b738bfc9961405cd90d99985fca93c58cc813f113ddce0c1ba01029",
    "log_sha256": "20e79a7f97aff29694b025bab1bf611ac67aab20c4fdfe1367150dda1da7dbd6",
    "seen_pids": [
      135397,
      135403
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.wait_ready_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_one_step",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_all_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.preflight_parent_active",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_drive_constructs_common_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_children_pipeline",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_prefix",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_lookup",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_preparation_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.four_ports_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:25:50.849594+00:00",
    "wall_seconds": 2.4328901010012487,
    "exit": 1,
    "peak_aggregate_rss_bytes": 954515456,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "b2073ed56a9e1e549ad13e02ae0ec6cb5bcb70a8809537e02aaf4364c5fc7ee7",
    "log_sha256": "cea00249864cc15f1f0e27a812fcee701acd352304821fda67c5dcc223a32d15",
    "seen_pids": [
      137760,
      137762,
      137767,
      137771,
      137774,
      137781
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.wait_ready_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_one_step",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_all_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.preflight_parent_active",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_drive_constructs_common_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_children_pipeline",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_prefix",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_lookup",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_commit_rearms",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_preparation_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.four_ports_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:27:40.987375+00:00",
    "wall_seconds": 21.338735161996738,
    "exit": 0,
    "peak_aggregate_rss_bytes": 1165283328,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "2afd111cd4fc998cc92e381bf1e5b9641cfbe09f23f0c5eb60c7d6ab87f3d381",
    "log_sha256": "d3441d6c41606cfb71e36f90d59c148fc74b96f77ab699613df6737789fa7119",
    "seen_pids": [
      138624,
      138626,
      138630,
      138634,
      138637,
      138644,
      138709,
      138715
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.wait_ready_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.ready_preparation",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_one_step",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_all_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.preflight_parent_active",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emission_preparation_stays_complete",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_drive_constructs_common_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_children_pipeline",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_prefix",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_lookup",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_commit_rearms",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_preparation_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.four_ports_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:30:06.996844+00:00",
    "wall_seconds": 5.659071396003128,
    "exit": 0,
    "peak_aggregate_rss_bytes": 1165291520,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "0ad99a8ec7d4bb72648ddca3971fbd9fb7a29d0b4d9d35ee7986e0b2651110fc",
    "log_sha256": "aa22b511defa01de5d82b916276b28bd892b76424d08d4598ffae47ae80e3487",
    "seen_pids": [
      139676,
      139678,
      139682,
      139686,
      139689,
      139696,
      139706,
      139710
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.wait_ready_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.ready_preparation",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_one_step",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_all_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.preflight_parent_active",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emission_preparation_stays_complete",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_drive_constructs_common_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_children_pipeline",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_prefix",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_lookup",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_commit_rearms",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_preparation_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.four_ports_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history",
      "--theorem",
      "YulangClosure.NativeValueDrain.context_execution_native_drive",
      "--theorem",
      "YulangClosure.NativeValueDrain.context_value_pipeline"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:39:06.758090+00:00",
    "wall_seconds": 9.284204527000838,
    "exit": 1,
    "peak_aggregate_rss_bytes": 1040695296,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "4f3517feb36e60f7f92d660fe909aed642ec465efa5546a1d4f126b16d2513b2",
    "log_sha256": "69e177bce236c27b663224de8529ba6f95912233512340eb6761276fb7d1ae91",
    "seen_pids": [
      142938,
      142940,
      142944,
      142948,
      142951,
      142958,
      142986
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.wait_ready_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.ready_preparation",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_one_step",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_all_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.preflight_parent_active",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emission_preparation_stays_complete",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_drive_constructs_common_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_children_pipeline",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_prefix",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_lookup",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_commit_rearms",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_preparation_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.four_ports_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history",
      "--theorem",
      "YulangClosure.NativeValueDrain.context_execution_native_drive",
      "--theorem",
      "YulangClosure.NativeValueDrain.context_value_pipeline"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:39:33.521129+00:00",
    "wall_seconds": 4.5480457410012605,
    "exit": 1,
    "peak_aggregate_rss_bytes": 956616704,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "9fcad853318917e429b216779b858601ceab1cfc00ba691722aa2514f2d22ede",
    "log_sha256": "a4a1939342943021180d1ad2c67060cd8ffc619db1386fe6d5fd7e587114b49a",
    "seen_pids": [
      143194,
      143197,
      143201,
      143205,
      143208,
      143215
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "python3",
      "/workspace/scratch/f98087c7ac1a/yulang/.agents/skills/yulang-lean-proofs/scripts/check_lean.py",
      "--project",
      "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
      "--lake",
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--timeout",
      "115",
      "--module",
      "YulangClosure.NativeValueDrain",
      "--theorem",
      "YulangClosure.NativeValueDrain.wait_ready_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.ready_preparation",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_one_step",
      "--theorem",
      "YulangClosure.NativeValueDrain.control_run_trans",
      "--theorem",
      "YulangClosure.NativeValueDrain.prepare_all_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.issuance_kept",
      "--theorem",
      "YulangClosure.NativeValueDrain.preflight_parent_active",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_admission",
      "--theorem",
      "YulangClosure.NativeValueDrain.active_after_enqueue",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_control",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_cursor",
      "--theorem",
      "YulangClosure.NativeValueDrain.start_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_invariant",
      "--theorem",
      "YulangClosure.NativeValueDrain.emission_preparation_stays_complete",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_constructs_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.emit_cursor_exact",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_drive_constructs_common_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.completed_issuance",
      "--theorem",
      "YulangClosure.NativeValueDrain.step_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.run_keeps_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.emitted_children_returned",
      "--theorem",
      "YulangClosure.NativeValueDrain.native_children_pipeline",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_prefix",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_parent_lookup",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_commit_rearms",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.actual_preparation_run",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.four_ports_issued",
      "--theorem",
      "YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history",
      "--theorem",
      "YulangClosure.NativeValueDrain.context_execution_native_drive",
      "--theorem",
      "YulangClosure.NativeValueDrain.context_value_pipeline"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:40:13.031088+00:00",
    "wall_seconds": 8.256039002000762,
    "exit": 0,
    "peak_aggregate_rss_bytes": 1169854464,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "826fa025241835aad606434b3d0fee2406b694d72ca1dbf03a618f3e61d1b095",
    "log_sha256": "89df83605acbec0911407aaeb007aeec62e3849e8cd332cef51557ba1c4395b4",
    "seen_pids": [
      143397,
      143399,
      143403,
      143407,
      143410,
      143417,
      143429,
      143433
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  },
  {
    "command": [
      "/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake",
      "--no-cache",
      "env",
      "lean",
      "-j1",
      "-M1024",
      "AuditNativeValueDrain.lean"
    ],
    "cwd": "/workspace/scratch/f98087c7ac1a/value-drain-r4/project",
    "started_utc": "2026-10-26T12:40:35.844632+00:00",
    "wall_seconds": 1.7154385059984634,
    "exit": 0,
    "peak_aggregate_rss_bytes": 1149829120,
    "cpu_affinity": [
      8
    ],
    "termination": null,
    "source_sha256": "826fa025241835aad606434b3d0fee2406b694d72ca1dbf03a618f3e61d1b095",
    "log_sha256": "edcc8b2417987283fdfdf2a1f588f9ccc189cdc8aba88706c082309ab778d2cf",
    "seen_pids": [
      143565,
      143572
    ],
    "lean_num_threads": 1,
    "lean_memory_mib": 1024,
    "outer_timeout_seconds": 119,
    "helper_timeout_seconds": 115,
    "aggregate_rss_ceiling_mib": 1280
  }
]
```

## Complete originating theorem types and axiom reports

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.prepareAll.match_1.eq_1

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.prepareAll.match_1.eq_1 : ∀
  (motive : Nat → YulangClosure.NativeValueDrain.Control → Sort u_1) (state : YulangClosure.NativeValueDrain.Control)
  (h_1 : (state : YulangClosure.NativeValueDrain.Control) → motive 0 state)
  (h_2 : (fuel : Nat) → (state : YulangClosure.NativeValueDrain.Control) → motive fuel.succ state),
  (match 0, state with
    | 0, state => h_1 state
    | fuel.succ, state => h_2 fuel state) =
    h_1 state
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.prepareAll.match_1.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.Invariant.queue

```text
@YulangClosure.NativeValueDrain.Invariant.queue : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    state.control.queue =
      List.map YulangClosure.NativeValueDrain.Issuance.occurrence state.receipts.reverse ++ origin.control.queue
'YulangClosure.NativeValueDrain.Invariant.queue' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Issuance.mk.injEq

```text
YulangClosure.NativeValueDrain.Issuance.mk.injEq : ∀ (port : YulangClosure.NativeValueDrain.PortWork)
  (occurrence : YulangClosure.NativeValueDrain.NativeOccurrence) (port_1 : YulangClosure.NativeValueDrain.PortWork)
  (occurrence_1 : YulangClosure.NativeValueDrain.NativeOccurrence),
  ({ port := port, occurrence := occurrence } = { port := port_1, occurrence := occurrence_1 }) =
    (port = port_1 ∧ occurrence = occurrence_1)
'YulangClosure.NativeValueDrain.Issuance.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.emit_cursor_exact

```text
YulangClosure.NativeValueDrain.emit_cursor_exact : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool) (fuel : Nat)
  (state : YulangClosure.NativeValueDrain.State),
  Option.map YulangClosure.NativeValueDrain.State.cursor
      (YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel state) =
    YulangClosure.NativeValuePorts.drive views qv qe parent post derived fuel state.cursor
'YulangClosure.NativeValueDrain.emit_cursor_exact' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.State.mk.injEq

```text
YulangClosure.NativeValueDrain.State.mk.injEq : ∀ (cursor : YulangClosure.NativeValuePorts.Cursor)
  (control : YulangClosure.NativeValueDrain.Control) (tasks : List YulangClosure.NativeValuePorts.Pair)
  (receipts : List YulangClosure.NativeValueDrain.Issuance) (cursor_1 : YulangClosure.NativeValuePorts.Cursor)
  (control_1 : YulangClosure.NativeValueDrain.Control) (tasks_1 : List YulangClosure.NativeValuePorts.Pair)
  (receipts_1 : List YulangClosure.NativeValueDrain.Issuance),
  ({ cursor := cursor, control := control, tasks := tasks, receipts := receipts } =
      { cursor := cursor_1, control := control_1, tasks := tasks_1, receipts := receipts_1 }) =
    (cursor = cursor_1 ∧ control = control_1 ∧ tasks = tasks_1 ∧ receipts = receipts_1)
'YulangClosure.NativeValueDrain.State.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Invariant.mapped

```text
@YulangClosure.NativeValueDrain.Invariant.mapped : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    ∀ (record : YulangClosure.NativeValueDrain.Issuance),
      record ∈ state.receipts → YulangClosure.NativeValueDrain.Issuance.matches state.tasks record
'YulangClosure.NativeValueDrain.Invariant.mapped' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history

```text
YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history : ∃ state,
  YulangClosure.NativeValueDrain.Witness.completed = Option.some state ∧
    YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial state.control ∧
      state.cursor.todo = []
'YulangClosure.NativeValueDrain.Witness.original_native_drive_has_shared_history' depends on axioms: [propext,
 Quot.sound]
```

### YulangClosure.NativeValueDrain.start_invariant

```text
YulangClosure.NativeValueDrain.start_invariant : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool)
  (origin : YulangClosure.NativeValueDrain.Origin),
  YulangClosure.NativeValueDrain.Active parent (YulangClosure.NativeValueDrain.start origin) →
    YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin
      (YulangClosure.NativeValueDrain.start origin)
'YulangClosure.NativeValueDrain.start_invariant' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.start.eq_1

```text
YulangClosure.NativeValueDrain.start.eq_1 : ∀ (origin : YulangClosure.NativeValueDrain.Origin),
  YulangClosure.NativeValueDrain.start origin =
    { cursor := YulangClosure.NativeValuePorts.initialCursor origin.arena origin.children [], control := origin.control,
      tasks := origin.tasks }
'YulangClosure.NativeValueDrain.start.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.step_invariant._simp_1_2

```text
@YulangClosure.NativeValueDrain.step_invariant._simp_1_2 : ∀ {α : Type u_1} {a : α} {s t : List α},
  (a ∈ s ++ t) = (a ∈ s ∨ a ∈ t)
'YulangClosure.NativeValueDrain.step_invariant._simp_1_2' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Invariant.cursor

```text
@YulangClosure.NativeValueDrain.Invariant.cursor : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    YulangClosure.NativeValuePorts.CursorValid views qv qe parent post derived origin.children [] state.cursor
'YulangClosure.NativeValueDrain.Invariant.cursor' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Witness.actual_parent_prefix

```text
YulangClosure.NativeValueDrain.Witness.actual_parent_prefix : YulangClosure.NativeDrainOwnership.Run
  YulangClosure.NativeDrainOwnership.initial YulangClosure.NativeValueDrain.Witness.origin.control
'YulangClosure.NativeValueDrain.Witness.actual_parent_prefix' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.prepareAll.match_1.eq_2

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.prepareAll.match_1.eq_2 : ∀
  (motive : Nat → YulangClosure.NativeValueDrain.Control → Sort u_1) (fuel : Nat)
  (state : YulangClosure.NativeValueDrain.Control)
  (h_1 : (state : YulangClosure.NativeValueDrain.Control) → motive 0 state)
  (h_2 : (fuel : Nat) → (state : YulangClosure.NativeValueDrain.Control) → motive fuel.succ state),
  (match fuel.succ, state with
    | 0, state => h_1 state
    | fuel.succ, state => h_2 fuel state) =
    h_2 fuel state
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.prepareAll.match_1.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.Invariant.tasks

```text
@YulangClosure.NativeValueDrain.Invariant.tasks : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    YulangClosure.NativeValuePorts.Extends origin.tasks state.tasks
'YulangClosure.NativeValueDrain.Invariant.tasks' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Origin.mk.inj

```text
@YulangClosure.NativeValueDrain.Origin.mk.inj : ∀ {arena : YulangClosure.NativeValuePorts.Arena}
  {children : List YulangClosure.NativeValuePorts.Child} {control : YulangClosure.NativeValueDrain.Control}
  {tasks : List YulangClosure.NativeValuePorts.Pair} {arena_1 : YulangClosure.NativeValuePorts.Arena}
  {children_1 : List YulangClosure.NativeValuePorts.Child} {control_1 : YulangClosure.NativeValueDrain.Control}
  {tasks_1 : List YulangClosure.NativeValuePorts.Pair},
  { arena := arena, children := children, control := control, tasks := tasks } =
      { arena := arena_1, children := children_1, control := control_1, tasks := tasks_1 } →
    arena = arena_1 ∧ children = children_1 ∧ control = control_1 ∧ tasks = tasks_1
'YulangClosure.NativeValueDrain.Origin.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.active_after_admission

```text
@YulangClosure.NativeValueDrain.active_after_admission : ∀ {parent : YulangClosure.NativeValuePorts.Key}
  {state : YulangClosure.NativeValueDrain.State} {arena : YulangClosure.NativeValuePorts.Arena}
  {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValueDrain.Active parent state →
    state.cursor.arena.Extends arena → YulangClosure.NativeValueDrain.Active parent (state.admitted arena receipt)
'YulangClosure.NativeValueDrain.active_after_admission' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.prepareAll.eq_1

```text
YulangClosure.NativeValueDrain.prepareAll.eq_1 : ∀ (x : YulangClosure.NativeValueDrain.Control),
  YulangClosure.NativeValueDrain.prepareAll 0 x =
    if YulangClosure.NativeValueDrain.ready x = Bool.true then Option.some x else Option.none
'YulangClosure.NativeValueDrain.prepareAll.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.run_invariant

```text
@YulangClosure.NativeValueDrain.run_invariant : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {first last : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Run views qv qe parent post derived first last →
    YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin first →
      YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin last
'YulangClosure.NativeValueDrain.run_invariant' depends on axioms: [propext, Quot.sound]
```

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_3.eq_2

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_3.eq_2 : ∀
  (motive : Option YulangClosure.NativeValuePorts.Receipt → Sort u_1) (receipt : YulangClosure.NativeValuePorts.Receipt)
  (h_1 : Unit → motive Option.none)
  (h_2 : (receipt : YulangClosure.NativeValuePorts.Receipt) → motive (Option.some receipt)),
  (match Option.some receipt with
    | Option.none => h_1 ()
    | Option.some receipt => h_2 receipt) =
    h_2 receipt
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_3.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.run_keeps_issued

```text
@YulangClosure.NativeValueDrain.run_keeps_issued : ∀ {first last : YulangClosure.NativeValueDrain.Control},
  YulangClosure.NativeDrainOwnership.Run first last →
    ∀ {work : YulangClosure.NativeValueDrain.NativeOccurrence}, work ∈ first.issued → work ∈ last.issued
'YulangClosure.NativeValueDrain.run_keeps_issued' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_1

```text
YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_1 : ∀ (a : YulangClosure.NativeValueDrain.PortWork)
  (a_1 : YulangClosure.NativeValueDrain.NativeOccurrence),
  { port := a, occurrence := a_1 } = { port := a, occurrence := a_1 }
'YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.step_cursor

```text
@YulangClosure.NativeValueDrain.step_cursor : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {first last : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Step views qv qe parent post derived first last →
    YulangClosure.NativeValuePorts.DispatchStep views qv qe parent post derived first.cursor last.cursor
'YulangClosure.NativeValueDrain.step_cursor' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.emission_preparation_stays_complete

```text
@YulangClosure.NativeValueDrain.emission_preparation_stays_complete : ∀ {views : Nat → Option (Option Nat)}
  {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {first last : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Run views qv qe parent post derived first last →
    YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin first →
      ∀ (fuel : Nat), YulangClosure.NativeValueDrain.prepareAll fuel last.control = Option.some last.control
'YulangClosure.NativeValueDrain.emission_preparation_stays_complete' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.ready.eq_1

```text
YulangClosure.NativeValueDrain.ready.eq_1 : ∀ (state : YulangClosure.NativeValueDrain.Control),
  YulangClosure.NativeValueDrain.ready state =
    match state.frames with
    | [] => Bool.false
    | frame :: rest =>
      Decidable.decide
        (frame.index = rest.length ∧ frame.completed ≤ frame.prepared ∧ frame.prepared = frame.acks.length)
'YulangClosure.NativeValueDrain.ready.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.step_keeps_issued

```text
@YulangClosure.NativeValueDrain.step_keeps_issued : ∀ {first last : YulangClosure.NativeValueDrain.Control},
  YulangClosure.NativeDrainOwnership.Step first last →
    ∀ {work : YulangClosure.NativeValueDrain.NativeOccurrence}, work ∈ first.issued → work ∈ last.issued
'YulangClosure.NativeValueDrain.step_keeps_issued' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Invariant.issued

```text
@YulangClosure.NativeValueDrain.Invariant.issued : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    state.control.issued =
      origin.control.issued ++ List.map YulangClosure.NativeValueDrain.Issuance.occurrence state.receipts
'YulangClosure.NativeValueDrain.Invariant.issued' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.State.mk.sizeOf_spec

```text
YulangClosure.NativeValueDrain.State.mk.sizeOf_spec : ∀ (cursor : YulangClosure.NativeValuePorts.Cursor)
  (control : YulangClosure.NativeValueDrain.Control) (tasks : List YulangClosure.NativeValuePorts.Pair)
  (receipts : List YulangClosure.NativeValueDrain.Issuance),
  SizeOf.sizeOf { cursor := cursor, control := control, tasks := tasks, receipts := receipts } =
    1 + SizeOf.sizeOf cursor + SizeOf.sizeOf control + SizeOf.sizeOf tasks + SizeOf.sizeOf receipts
'YulangClosure.NativeValueDrain.State.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.Witness.actual_parent_lookup

```text
YulangClosure.NativeValueDrain.Witness.actual_parent_lookup : YulangClosure.NativeValueDrain.Active
  YulangClosure.NativeValuePorts.Witness.parent
  (YulangClosure.NativeValueDrain.start YulangClosure.NativeValueDrain.Witness.origin)
'YulangClosure.NativeValueDrain.Witness.actual_parent_lookup' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.emit.eq_1

```text
YulangClosure.NativeValueDrain.emit.eq_1 : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool)
  (x : YulangClosure.NativeValueDrain.State),
  YulangClosure.NativeValueDrain.emit views qv qe parent post derived 0 x =
    if x.cursor.todo = [] then Option.some x else Option.none
'YulangClosure.NativeValueDrain.emit.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Issuance.mk.sizeOf_spec

```text
YulangClosure.NativeValueDrain.Issuance.mk.sizeOf_spec : ∀ (port : YulangClosure.NativeValueDrain.PortWork)
  (occurrence : YulangClosure.NativeValueDrain.NativeOccurrence),
  SizeOf.sizeOf { port := port, occurrence := occurrence } = 1 + SizeOf.sizeOf port + SizeOf.sizeOf occurrence
'YulangClosure.NativeValueDrain.Issuance.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.Witness.actual_preparation_run

```text
YulangClosure.NativeValueDrain.Witness.actual_preparation_run : YulangClosure.NativeDrainOwnership.Run
  YulangClosure.NativeValueDrain.Witness.afterCommit YulangClosure.NativeDrainOwnership.Witness.transported
'YulangClosure.NativeValueDrain.Witness.actual_preparation_run' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.step_invariant

```text
@YulangClosure.NativeValueDrain.step_invariant : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {first last : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Step views qv qe parent post derived first last →
    YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin first →
      YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin last
'YulangClosure.NativeValueDrain.step_invariant' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.Invariant.next

```text
@YulangClosure.NativeValueDrain.Invariant.next : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    state.control.nextWork = origin.control.nextWork + state.receipts.length
'YulangClosure.NativeValueDrain.Invariant.next' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.step_invariant._simp_1_3

```text
@YulangClosure.NativeValueDrain.step_invariant._simp_1_3 : ∀ {α : Type u_1} {a b : α}, (a ∈ [b]) = (a = b)
'YulangClosure.NativeValueDrain.step_invariant._simp_1_3' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Invariant.records

```text
@YulangClosure.NativeValueDrain.Invariant.records : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    List.map YulangClosure.NativeValueDrain.Issuance.port state.receipts = state.cursor.records
'YulangClosure.NativeValueDrain.Invariant.records' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.ready_preparation

```text
YulangClosure.NativeValueDrain.ready_preparation : ∀ (fuel : Nat) (state : YulangClosure.NativeValueDrain.Control),
  YulangClosure.NativeValueDrain.ready state = Bool.true →
    YulangClosure.NativeValueDrain.prepareAll fuel state = Option.some state
'YulangClosure.NativeValueDrain.ready_preparation' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_3.eq_1

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_3.eq_1 : ∀
  (motive : Option YulangClosure.NativeValuePorts.Receipt → Sort u_1) (h_1 : Unit → motive Option.none)
  (h_2 : (receipt : YulangClosure.NativeValuePorts.Receipt) → motive (Option.some receipt)),
  (match Option.none with
    | Option.none => h_1 ()
    | Option.some receipt => h_2 receipt) =
    h_1 ()
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_3.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.Issuance.mk.inj

```text
@YulangClosure.NativeValueDrain.Issuance.mk.inj : ∀ {port : YulangClosure.NativeValueDrain.PortWork}
  {occurrence : YulangClosure.NativeValueDrain.NativeOccurrence} {port_1 : YulangClosure.NativeValueDrain.PortWork}
  {occurrence_1 : YulangClosure.NativeValueDrain.NativeOccurrence},
  { port := port, occurrence := occurrence } = { port := port_1, occurrence := occurrence_1 } →
    port = port_1 ∧ occurrence = occurrence_1
'YulangClosure.NativeValueDrain.Issuance.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.Invariant.serials

```text
@YulangClosure.NativeValueDrain.Invariant.serials : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    List.map (fun record => record.occurrence.serial) state.receipts =
      List.range' origin.control.nextWork state.receipts.length
'YulangClosure.NativeValueDrain.Invariant.serials' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.State.admitted.eq_1

```text
YulangClosure.NativeValueDrain.State.admitted.eq_1 : ∀ (state : YulangClosure.NativeValueDrain.State)
  (arena : YulangClosure.NativeValuePorts.Arena) (receipt : YulangClosure.NativeValuePorts.Receipt),
  state.admitted arena receipt =
    { cursor := state.cursor.admitted arena receipt, control := state.control, tasks := state.tasks,
      receipts := state.receipts }
'YulangClosure.NativeValueDrain.State.admitted.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.active_after_enqueue

```text
@YulangClosure.NativeValueDrain.active_after_enqueue : ∀ {parent : YulangClosure.NativeValuePorts.Key}
  {state : YulangClosure.NativeValueDrain.State} {child : YulangClosure.NativeValuePorts.Child}
  {rest : List YulangClosure.NativeValuePorts.Child} {receipt : YulangClosure.NativeValuePorts.Receipt},
  YulangClosure.NativeValueDrain.Active parent state →
    YulangClosure.NativeValueDrain.Active parent (state.enqueued child rest receipt)
'YulangClosure.NativeValueDrain.active_after_enqueue' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_1.eq_1

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_1.eq_1 : ∀
  (motive : YulangClosure.NativeValuePorts.Arena × YulangClosure.NativeValuePorts.Receipt → Sort u_1)
  (arena : YulangClosure.NativeValuePorts.Arena) (receipt : YulangClosure.NativeValuePorts.Receipt)
  (h_1 :
    (arena : YulangClosure.NativeValuePorts.Arena) →
      (receipt : YulangClosure.NativeValuePorts.Receipt) → motive (arena, receipt)),
  (match (arena, receipt) with
    | (arena, receipt) => h_1 arena receipt) =
    h_1 arena receipt
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_1.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.wait_ready_exact

```text
YulangClosure.NativeValueDrain.wait_ready_exact : ∀ (operation : YulangClosure.NativeDrainOwnership.Operation)
  (ticket : YulangClosure.NativeDrainOwnership.Ticket),
  YulangClosure.NativeValueDrain.waitReady operation ticket = Bool.true ↔
    YulangClosure.NativeDrainOwnership.completionWait operation ticket
'YulangClosure.NativeValueDrain.wait_ready_exact' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.context_value_pipeline

```text
@YulangClosure.NativeValueDrain.context_value_pipeline : ∀ {contexts : YulangClosure.NativeContextExpansion.Tables}
  {contextFuel : Nat} {tables : YulangClosure.NativeValueStructure.Tables}
  {routing : YulangClosure.NativeValueStructure.Routing} {request : YulangClosure.NativeValueStructure.Request}
  {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {preparationFuel portFuel : Nat}
  {prepared : YulangClosure.NativeValueDrain.Control} {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial origin.control →
    YulangClosure.NativeValueDrain.ParentPresent request.key (YulangClosure.NativeValueDrain.start origin) →
      YulangClosure.NativeValueDrain.prepareAll preparationFuel origin.control = Option.some prepared →
        YulangClosure.NativeValueStructure.executeAfterContext contexts contextFuel tables routing request views qv qe
              post derived portFuel origin.arena [] =
            Option.some cursor →
          request.transformer = 0 ∧
            routing.candidate = Bool.true ∧
              ∃ family items emitted,
                YulangClosure.NativeValueStructure.dispatch tables routing request =
                    YulangClosure.NativeValueStructure.Route.body
                      (YulangClosure.NativeValueStructure.Local.children family items) ∧
                  emitted.cursor = cursor ∧
                    YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial emitted.control ∧
                      ∀ (last : YulangClosure.NativeDrainOwnership.State),
                        YulangClosure.NativeDrainOwnership.Run emitted.control last →
                          last.queue = [] →
                            last.frames = [] →
                              ∃ jobs,
                                List.map (fun job => job.port.source) jobs = items ∧
                                  ∀ (job : YulangClosure.NativeValueDrain.Issuance),
                                    job ∈ jobs →
                                      YulangClosure.NativeValueDrain.Issuance.matches emitted.tasks job ∧
                                        YulangClosure.NativeValuePorts.AdmissionResult emitted.cursor.arena views qv qe
                                            request.key post derived job.port.source job.port.receipt ∧
                                          ∃ returned,
                                            returned ∈ last.returns ∧
                                              job.occurrence ∈ returned.frame.processed ∧
                                                returned.frame.diagnosed = Bool.true ∧
                                                  returned.frame.phase =
                                                      YulangClosure.NativeDrainOwnership.Phase.returnReady ∧
                                                    returned.frame.pending = [] ∧ returned.frame.current = Option.none
'YulangClosure.NativeValueDrain.context_value_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### YulangClosure.NativeValueDrain.control_run_trans

```text
@YulangClosure.NativeValueDrain.control_run_trans : ∀ {first middle last : YulangClosure.NativeValueDrain.Control},
  YulangClosure.NativeDrainOwnership.Run first middle →
    YulangClosure.NativeDrainOwnership.Run middle last → YulangClosure.NativeDrainOwnership.Run first last
'YulangClosure.NativeValueDrain.control_run_trans' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Origin.mk.injEq

```text
YulangClosure.NativeValueDrain.Origin.mk.injEq : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (children : List YulangClosure.NativeValuePorts.Child) (control : YulangClosure.NativeValueDrain.Control)
  (tasks : List YulangClosure.NativeValuePorts.Pair) (arena_1 : YulangClosure.NativeValuePorts.Arena)
  (children_1 : List YulangClosure.NativeValuePorts.Child) (control_1 : YulangClosure.NativeValueDrain.Control)
  (tasks_1 : List YulangClosure.NativeValuePorts.Pair),
  ({ arena := arena, children := children, control := control, tasks := tasks } =
      { arena := arena_1, children := children_1, control := control_1, tasks := tasks_1 }) =
    (arena = arena_1 ∧ children = children_1 ∧ control = control_1 ∧ tasks = tasks_1)
'YulangClosure.NativeValueDrain.Origin.mk.injEq' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.waitReady.eq_1

```text
YulangClosure.NativeValueDrain.waitReady.eq_1 : ∀ (operation : YulangClosure.NativeDrainOwnership.Operation)
  (ticket : YulangClosure.NativeDrainOwnership.Ticket),
  YulangClosure.NativeValueDrain.waitReady operation ticket =
    match operation.waiting with
    | YulangClosure.NativeDrainOwnership.Wait.idle => Bool.true
    | YulangClosure.NativeDrainOwnership.Wait.running actual frame =>
      Decidable.decide (actual = ticket ∧ operation.queued = ticket.index + 1)
    | YulangClosure.NativeDrainOwnership.Wait.ready ticket frame transitions => Bool.false
'YulangClosure.NativeValueDrain.waitReady.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.emit.eq_2

```text
YulangClosure.NativeValueDrain.emit.eq_2 : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool) (x : YulangClosure.NativeValueDrain.State)
  (fuel : Nat),
  YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel.succ x =
    match x.cursor.todo with
    | [] => Option.some x
    | child :: rest =>
      match x.cursor.pending with
      | Option.none => do
        let __x ← YulangClosure.NativeValuePorts.admit x.cursor.arena views qv qe parent post derived child
        match __x with
          | (arena, receipt) =>
            YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel (x.admitted arena receipt)
      | Option.some receipt =>
        YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel (x.enqueued child rest receipt)
'YulangClosure.NativeValueDrain.emit.eq_2' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Witness.actual_commit_rearms

```text
YulangClosure.NativeValueDrain.Witness.actual_commit_rearms : YulangClosure.NativeDrainOwnership.Step
  YulangClosure.NativeDrainOwnership.Witness.transported YulangClosure.NativeValueDrain.Witness.afterCommit
'YulangClosure.NativeValueDrain.Witness.actual_commit_rearms' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.issuance_kept

```text
@YulangClosure.NativeValueDrain.issuance_kept : ∀ {before after : List YulangClosure.NativeValuePorts.Pair},
  YulangClosure.NativeValuePorts.Extends before after →
    ∀ {record : YulangClosure.NativeValueDrain.Issuance},
      YulangClosure.NativeValueDrain.Issuance.matches before record →
        YulangClosure.NativeValueDrain.Issuance.matches after record
'YulangClosure.NativeValueDrain.issuance_kept' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValueDrain.0.Option.getD.match_1.eq_2

```text
@_private.YulangClosure.NativeValueDrain.0.Option.getD.match_1.eq_2 : ∀ {α : Type u_1} (motive : Option α → Sort u_2)
  (h_1 : (x : α) → motive (Option.some x)) (h_2 : Unit → motive Option.none),
  (match Option.none with
    | Option.some x => h_1 x
    | Option.none => h_2 ()) =
    h_2 ()
'_private.YulangClosure.NativeValueDrain.0.Option.getD.match_1.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.emitted_children_returned

```text
@YulangClosure.NativeValueDrain.emitted_children_returned : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {fuel : Nat} {emitted : YulangClosure.NativeValueDrain.State}
  {last : YulangClosure.NativeValueDrain.Control},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial origin.control →
    YulangClosure.NativeValueDrain.Active parent (YulangClosure.NativeValueDrain.start origin) →
      YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel
            (YulangClosure.NativeValueDrain.start origin) =
          Option.some emitted →
        YulangClosure.NativeDrainOwnership.Run emitted.control last →
          last.queue = [] →
            last.frames = [] →
              ∃ jobs,
                List.map (fun job => job.port.source) jobs = origin.children ∧
                  ∀ (job : YulangClosure.NativeValueDrain.Issuance),
                    job ∈ jobs →
                      YulangClosure.NativeValueDrain.Issuance.matches emitted.tasks job ∧
                        YulangClosure.NativeValuePorts.AdmissionResult emitted.cursor.arena views qv qe parent post
                            derived job.port.source job.port.receipt ∧
                          ∃ returned,
                            returned ∈ last.returns ∧
                              job.occurrence ∈ returned.frame.processed ∧
                                returned.frame.diagnosed = Bool.true ∧
                                  returned.frame.phase = YulangClosure.NativeDrainOwnership.Phase.returnReady ∧
                                    returned.frame.pending = [] ∧ returned.frame.current = Option.none
'YulangClosure.NativeValueDrain.emitted_children_returned' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### YulangClosure.NativeValueStructure.executeChildren.eq_1

```text
YulangClosure.NativeValueStructure.executeChildren.eq_1 : ∀ (tables : YulangClosure.NativeValueStructure.Tables)
  (routing : YulangClosure.NativeValueStructure.Routing) (request : YulangClosure.NativeValueStructure.Request)
  (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat) (post : Nat) (derived : Bool) (fuel : Nat)
  (arena : YulangClosure.NativeValuePorts.Arena) (queue : List YulangClosure.NativeValuePorts.NativeWork),
  YulangClosure.NativeValueStructure.executeChildren tables routing request views qv qe post derived fuel arena queue =
    if routing.candidate = Bool.true then
      match YulangClosure.NativeValueStructure.dispatch tables routing request with
      |
      YulangClosure.NativeValueStructure.Route.body (YulangClosure.NativeValueStructure.Local.children family items) =>
        YulangClosure.NativeValuePorts.drive views qv qe request.key post derived fuel
          (YulangClosure.NativeValuePorts.initialCursor arena items queue)
      | x => Option.none
    else Option.none
'YulangClosure.NativeValueStructure.executeChildren.eq_1' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_7.eq_1

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_7.eq_1 : ∀
  (motive : Nat → YulangClosure.NativeValueDrain.State → Sort u_1) (state : YulangClosure.NativeValueDrain.State)
  (h_1 : (state : YulangClosure.NativeValueDrain.State) → motive 0 state)
  (h_2 : (fuel : Nat) → (state : YulangClosure.NativeValueDrain.State) → motive fuel.succ state),
  (match 0, state with
    | 0, state => h_1 state
    | fuel.succ, state => h_2 fuel state) =
    h_1 state
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_7.eq_1' does not depend on any axioms
```

### _private.YulangClosure.NativeValueDrain.0.Option.getD.match_1.eq_1

```text
@_private.YulangClosure.NativeValueDrain.0.Option.getD.match_1.eq_1 : ∀ {α : Type u_1} (motive : Option α → Sort u_2)
  (x : α) (h_1 : (x : α) → motive (Option.some x)) (h_2 : Unit → motive Option.none),
  (match Option.some x with
    | Option.some x => h_1 x
    | Option.none => h_2 ()) =
    h_1 x
'_private.YulangClosure.NativeValueDrain.0.Option.getD.match_1.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.context_execution_native_drive

```text
@YulangClosure.NativeValueDrain.context_execution_native_drive : ∀
  {contexts : YulangClosure.NativeContextExpansion.Tables} {contextFuel : Nat}
  {tables : YulangClosure.NativeValueStructure.Tables} {routing : YulangClosure.NativeValueStructure.Routing}
  {request : YulangClosure.NativeValueStructure.Request} {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {post : Nat} {derived : Bool} {portFuel : Nat} {arena : YulangClosure.NativeValuePorts.Arena}
  {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValueStructure.executeAfterContext contexts contextFuel tables routing request views qv qe post
        derived portFuel arena [] =
      Option.some cursor →
    request.transformer = 0 ∧
      routing.candidate = Bool.true ∧
        ∃ family items,
          YulangClosure.NativeValueStructure.dispatch tables routing request =
              YulangClosure.NativeValueStructure.Route.body
                (YulangClosure.NativeValueStructure.Local.children family items) ∧
            YulangClosure.NativeValuePorts.drive views qv qe request.key post derived portFuel
                (YulangClosure.NativeValuePorts.initialCursor arena items []) =
              Option.some cursor
'YulangClosure.NativeValueDrain.context_execution_native_drive' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.native_children_pipeline

```text
@YulangClosure.NativeValueDrain.native_children_pipeline : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {preparationFuel portFuel : Nat}
  {prepared : YulangClosure.NativeValueDrain.Control} {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial origin.control →
    YulangClosure.NativeValueDrain.ParentPresent parent (YulangClosure.NativeValueDrain.start origin) →
      YulangClosure.NativeValueDrain.prepareAll preparationFuel origin.control = Option.some prepared →
        YulangClosure.NativeValuePorts.drive views qv qe parent post derived portFuel
              (YulangClosure.NativeValuePorts.initialCursor origin.arena origin.children []) =
            Option.some cursor →
          ∃ emitted,
            emitted.cursor = cursor ∧
              YulangClosure.NativeDrainOwnership.Run YulangClosure.NativeDrainOwnership.initial emitted.control ∧
                ∀ (last : YulangClosure.NativeDrainOwnership.State),
                  YulangClosure.NativeDrainOwnership.Run emitted.control last →
                    last.queue = [] →
                      last.frames = [] →
                        ∃ jobs,
                          List.map (fun job => job.port.source) jobs = origin.children ∧
                            ∀ (job : YulangClosure.NativeValueDrain.Issuance),
                              job ∈ jobs →
                                YulangClosure.NativeValueDrain.Issuance.matches emitted.tasks job ∧
                                  YulangClosure.NativeValuePorts.AdmissionResult emitted.cursor.arena views qv qe parent
                                      post derived job.port.source job.port.receipt ∧
                                    ∃ returned,
                                      returned ∈ last.returns ∧
                                        job.occurrence ∈ returned.frame.processed ∧
                                          returned.frame.diagnosed = Bool.true ∧
                                            returned.frame.phase =
                                                YulangClosure.NativeDrainOwnership.Phase.returnReady ∧
                                              returned.frame.pending = [] ∧ returned.frame.current = Option.none
'YulangClosure.NativeValueDrain.native_children_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### YulangClosure.NativeValueDrain.Invariant.frames

```text
@YulangClosure.NativeValueDrain.Invariant.frames : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    state.control.frames = origin.control.frames
'YulangClosure.NativeValueDrain.Invariant.frames' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Witness.four_ports_issued

```text
YulangClosure.NativeValueDrain.Witness.four_ports_issued : Option.map
    (fun state =>
      (state.receipts.length, List.map (fun record => record.occurrence.serial) state.receipts,
        List.map YulangClosure.NativeDrainOwnership.Work.serial state.control.queue, state.control.nextWork,
        state.control.transferred))
    YulangClosure.NativeValueDrain.Witness.completed =
  Option.some (4, [1, 2, 3, 4], [4, 3, 2, 1], 5, [])
'YulangClosure.NativeValueDrain.Witness.four_ports_issued' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack

```text
YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack : YulangClosure.NativeValueDrain.ready
      YulangClosure.NativeValueDrain.Witness.afterCommit =
    Bool.false ∧
  YulangClosure.NativeValueDrain.prepareAll 1 YulangClosure.NativeValueDrain.Witness.afterCommit =
    Option.some YulangClosure.NativeDrainOwnership.Witness.transported
'YulangClosure.NativeValueDrain.Witness.commit_reprepares_actual_ack' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.State.mk.inj

```text
@YulangClosure.NativeValueDrain.State.mk.inj : ∀ {cursor : YulangClosure.NativeValuePorts.Cursor}
  {control : YulangClosure.NativeValueDrain.Control} {tasks : List YulangClosure.NativeValuePorts.Pair}
  {receipts : List YulangClosure.NativeValueDrain.Issuance} {cursor_1 : YulangClosure.NativeValuePorts.Cursor}
  {control_1 : YulangClosure.NativeValueDrain.Control} {tasks_1 : List YulangClosure.NativeValuePorts.Pair}
  {receipts_1 : List YulangClosure.NativeValueDrain.Issuance},
  { cursor := cursor, control := control, tasks := tasks, receipts := receipts } =
      { cursor := cursor_1, control := control_1, tasks := tasks_1, receipts := receipts_1 } →
    cursor = cursor_1 ∧ control = control_1 ∧ tasks = tasks_1 ∧ receipts = receipts_1
'YulangClosure.NativeValueDrain.State.mk.inj' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.Invariant.arena

```text
@YulangClosure.NativeValueDrain.Invariant.arena : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    origin.arena.Extends state.cursor.arena
'YulangClosure.NativeValueDrain.Invariant.arena' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.emit_constructs_run

```text
@YulangClosure.NativeValueDrain.emit_constructs_run : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool} {fuel : Nat}
  {origin : YulangClosure.NativeValueDrain.Origin} {first last : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin first →
    YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel first = Option.some last →
      YulangClosure.NativeValueDrain.Run views qv qe parent post derived first last ∧ last.cursor.todo = []
'YulangClosure.NativeValueDrain.emit_constructs_run' depends on axioms: [propext, Quot.sound]
```

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_7.eq_2

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_7.eq_2 : ∀
  (motive : Nat → YulangClosure.NativeValueDrain.State → Sort u_1) (fuel : Nat)
  (state : YulangClosure.NativeValueDrain.State) (h_1 : (state : YulangClosure.NativeValueDrain.State) → motive 0 state)
  (h_2 : (fuel : Nat) → (state : YulangClosure.NativeValueDrain.State) → motive fuel.succ state),
  (match fuel.succ, state with
    | 0, state => h_1 state
    | fuel.succ, state => h_2 fuel state) =
    h_2 fuel state
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_7.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_2

```text
YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_2 : ∀ (a : YulangClosure.NativeValueDrain.PortWork)
  (a_1 b : YulangClosure.NativeValueDrain.NativeOccurrence),
  ¬a_1 = b → { port := a, occurrence := a_1 } = { port := a, occurrence := b } → False
'YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_2' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.prepareOne.eq_1

```text
YulangClosure.NativeValueDrain.prepareOne.eq_1 : ∀ (state : YulangClosure.NativeValueDrain.Control),
  YulangClosure.NativeValueDrain.prepareOne state =
    match state.frames with
    | frame :: rest =>
      if frame.index = rest.length ∧ frame.completed ≤ frame.prepared ∧ frame.prepared < frame.acks.length then do
        let ticket ← frame.acks[frame.prepared]?
        let operation ← state.operations ticket.operation
        if
              operation.consumed ≤ ticket.index ∧
                ticket.index < operation.queued ∧
                  YulangClosure.NativeValueDrain.waitReady operation ticket = Bool.true then
            Option.some
              { operations := state.operations, nextOperation := state.nextOperation, nextBirth := state.nextBirth,
                nextWork := state.nextWork, queue := state.queue,
                frames :=
                  { birth := frame.birth, index := frame.index, current := frame.current,
                      processing := frame.processing, processed := frame.processed, done := frame.done,
                      pending := frame.pending, prepared := frame.prepared + 1, phase := frame.phase,
                      diagnosed := frame.diagnosed, destination := frame.destination,
                      transitions := frame.transitions } ::
                    rest,
                issued := state.issued, transferred := state.transferred, acknowledgements := state.acknowledgements,
                returns := state.returns }
          else Option.none
      else Option.none
    | x => Option.none
'YulangClosure.NativeValueDrain.prepareOne.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Origin.mk.sizeOf_spec

```text
YulangClosure.NativeValueDrain.Origin.mk.sizeOf_spec : ∀ (arena : YulangClosure.NativeValuePorts.Arena)
  (children : List YulangClosure.NativeValuePorts.Child) (control : YulangClosure.NativeValueDrain.Control)
  (tasks : List YulangClosure.NativeValuePorts.Pair),
  SizeOf.sizeOf { arena := arena, children := children, control := control, tasks := tasks } =
    1 + SizeOf.sizeOf arena + SizeOf.sizeOf children + SizeOf.sizeOf control + SizeOf.sizeOf tasks
'YulangClosure.NativeValueDrain.Origin.mk.sizeOf_spec' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.prepareAll.eq_2

```text
YulangClosure.NativeValueDrain.prepareAll.eq_2 : ∀ (x : YulangClosure.NativeValueDrain.Control) (fuel : Nat),
  YulangClosure.NativeValueDrain.prepareAll fuel.succ x =
    if YulangClosure.NativeValueDrain.ready x = Bool.true then Option.some x
    else (YulangClosure.NativeValueDrain.prepareOne x).bind (YulangClosure.NativeValueDrain.prepareAll fuel)
'YulangClosure.NativeValueDrain.prepareAll.eq_2' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_5.eq_1

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_5.eq_1 : ∀
  (motive : List YulangClosure.NativeValuePorts.Child → Sort u_1) (h_1 : Unit → motive [])
  (h_2 :
    (child : YulangClosure.NativeValuePorts.Child) →
      (rest : List YulangClosure.NativeValuePorts.Child) → motive (child :: rest)),
  (match [] with
    | [] => h_1 ()
    | child :: rest => h_2 child rest) =
    h_1 ()
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_5.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.prepare_one_step

```text
@YulangClosure.NativeValueDrain.prepare_one_step : ∀ {before after : YulangClosure.NativeValueDrain.Control},
  YulangClosure.NativeValueDrain.prepareOne before = Option.some after →
    YulangClosure.NativeDrainOwnership.Step before after ∧
      ∃ frame rest,
        before.frames = frame :: rest ∧
          after =
            { operations := before.operations, nextOperation := before.nextOperation, nextBirth := before.nextBirth,
              nextWork := before.nextWork, queue := before.queue,
              frames :=
                { birth := frame.birth, index := frame.index, current := frame.current, processing := frame.processing,
                    processed := frame.processed, done := frame.done, pending := frame.pending,
                    prepared := frame.prepared + 1, phase := frame.phase, diagnosed := frame.diagnosed,
                    destination := frame.destination, transitions := frame.transitions } ::
                  rest,
              issued := before.issued, transferred := before.transferred, acknowledgements := before.acknowledgements,
              returns := before.returns }
'YulangClosure.NativeValueDrain.prepare_one_step' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.Run.brecOn

```text
@YulangClosure.NativeValueDrain.Run.brecOn : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {motive :
    (a a_1 : YulangClosure.NativeValueDrain.State) →
      YulangClosure.NativeValueDrain.Run views qv qe parent post derived a a_1 → Prop}
  {a a_1 : YulangClosure.NativeValueDrain.State}
  (t : YulangClosure.NativeValueDrain.Run views qv qe parent post derived a a_1),
  (∀ (a a_2 : YulangClosure.NativeValueDrain.State)
      (t : YulangClosure.NativeValueDrain.Run views qv qe parent post derived a a_2),
      YulangClosure.NativeValueDrain.Run.below t → motive a a_2 t) →
    motive a a_1 t
'YulangClosure.NativeValueDrain.Run.brecOn' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.prepare_all_exact

```text
@YulangClosure.NativeValueDrain.prepare_all_exact : ∀ {fuel : Nat}
  {before after : YulangClosure.NativeValueDrain.Control},
  YulangClosure.NativeValueDrain.prepareAll fuel before = Option.some after →
    YulangClosure.NativeDrainOwnership.Run before after ∧
      YulangClosure.NativeValueDrain.ready after = Bool.true ∧
        ∃ frame rest,
          before.frames = frame :: rest ∧
            after =
              { operations := before.operations, nextOperation := before.nextOperation, nextBirth := before.nextBirth,
                nextWork := before.nextWork, queue := before.queue,
                frames :=
                  { birth := frame.birth, index := frame.index, current := frame.current,
                      processing := frame.processing, processed := frame.processed, done := frame.done,
                      pending := frame.pending, prepared := frame.acks.length, phase := frame.phase,
                      diagnosed := frame.diagnosed, destination := frame.destination,
                      transitions := frame.transitions } ::
                    rest,
                issued := before.issued, transferred := before.transferred, acknowledgements := before.acknowledgements,
                returns := before.returns }
'YulangClosure.NativeValueDrain.prepare_all_exact' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_3

```text
YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_3 : ∀ (a : YulangClosure.NativeValueDrain.PortWork)
  (a_1 : YulangClosure.NativeValueDrain.NativeOccurrence) (b : YulangClosure.NativeValueDrain.PortWork)
  (b_1 : YulangClosure.NativeValueDrain.NativeOccurrence),
  ¬a = b → { port := a, occurrence := a_1 } = { port := b, occurrence := b_1 } → False
'YulangClosure.NativeValueDrain.instDecidableEqIssuance.decEq._proof_3' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.State.enqueued.eq_1

```text
YulangClosure.NativeValueDrain.State.enqueued.eq_1 : ∀ (state : YulangClosure.NativeValueDrain.State)
  (child : YulangClosure.NativeValuePorts.Child) (rest : List YulangClosure.NativeValuePorts.Child)
  (receipt : YulangClosure.NativeValuePorts.Receipt),
  state.enqueued child rest receipt =
    { cursor := state.cursor.enqueued child rest receipt,
      control :=
        YulangClosure.NativeDrainOwnership.pushWork state.control
          (YulangClosure.NativeDrainOwnership.work state.control
            (YulangClosure.NativeValuePorts.intern state.tasks child.task).snd receipt.relation Option.none)
          Bool.true,
      tasks := (YulangClosure.NativeValuePorts.intern state.tasks child.task).fst,
      receipts :=
        state.receipts ++
          [{ port := { source := child, receipt := receipt },
              occurrence :=
                YulangClosure.NativeDrainOwnership.work state.control
                  (YulangClosure.NativeValuePorts.intern state.tasks child.task).snd receipt.relation Option.none }] }
'YulangClosure.NativeValueDrain.State.enqueued.eq_1' depends on axioms: [propext]
```

### YulangClosure.NativeDrainOwnership.completionWait.eq_1

```text
YulangClosure.NativeDrainOwnership.completionWait.eq_1 : ∀ (op : YulangClosure.NativeDrainOwnership.Operation)
  (a : YulangClosure.NativeDrainOwnership.Ticket),
  YulangClosure.NativeDrainOwnership.completionWait op a =
    (op.waiting = YulangClosure.NativeDrainOwnership.Wait.idle ∨
      ∃ index, op.waiting = YulangClosure.NativeDrainOwnership.Wait.running a index ∧ op.queued = a.index + 1)
'YulangClosure.NativeDrainOwnership.completionWait.eq_1' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.completed_issuance

```text
@YulangClosure.NativeValueDrain.completed_issuance : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    state.cursor.todo = [] →
      state.cursor.pending = Option.none ∧
        ∃ jobs,
          List.map (fun job => job.port.source) jobs = origin.children ∧
            state.control.queue =
                List.map YulangClosure.NativeValueDrain.Issuance.occurrence jobs ++ origin.control.queue ∧
              state.control.issued =
                  origin.control.issued ++ List.map YulangClosure.NativeValueDrain.Issuance.occurrence jobs.reverse ∧
                ∀ (job : YulangClosure.NativeValueDrain.Issuance),
                  job ∈ jobs →
                    YulangClosure.NativeValueDrain.Issuance.matches state.tasks job ∧
                      YulangClosure.NativeValuePorts.AdmissionResult state.cursor.arena views qv qe parent post derived
                        job.port.source job.port.receipt
'YulangClosure.NativeValueDrain.completed_issuance' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.run_cursor

```text
@YulangClosure.NativeValueDrain.run_cursor : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {first last : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Run views qv qe parent post derived first last →
    YulangClosure.NativeValuePorts.DispatchRun views qv qe parent post derived first.cursor last.cursor
'YulangClosure.NativeValueDrain.run_cursor' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.Invariant.active

```text
@YulangClosure.NativeValueDrain.Invariant.active : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {state : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Invariant views qv qe parent post derived origin state →
    YulangClosure.NativeValueDrain.Active parent state
'YulangClosure.NativeValueDrain.Invariant.active' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.step_control

```text
@YulangClosure.NativeValueDrain.step_control : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {first last : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Step views qv qe parent post derived first last →
    YulangClosure.NativeDrainOwnership.Run first.control last.control
'YulangClosure.NativeValueDrain.step_control' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.run_control

```text
@YulangClosure.NativeValueDrain.run_control : ∀ {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
  {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {first last : YulangClosure.NativeValueDrain.State},
  YulangClosure.NativeValueDrain.Run views qv qe parent post derived first last →
    YulangClosure.NativeDrainOwnership.Run first.control last.control
'YulangClosure.NativeValueDrain.run_control' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.emit.eq_def

```text
YulangClosure.NativeValueDrain.emit.eq_def : ∀ (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
  (parent : YulangClosure.NativeValuePorts.Key) (post : Nat) (derived : Bool) (x : Nat)
  (x_1 : YulangClosure.NativeValueDrain.State),
  YulangClosure.NativeValueDrain.emit views qv qe parent post derived x x_1 =
    match x, x_1 with
    | 0, state => if state.cursor.todo = [] then Option.some state else Option.none
    | fuel.succ, state =>
      match state.cursor.todo with
      | [] => Option.some state
      | child :: rest =>
        match state.cursor.pending with
        | Option.none => do
          let __x ← YulangClosure.NativeValuePorts.admit state.cursor.arena views qv qe parent post derived child
          match __x with
            | (arena, receipt) =>
              YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel (state.admitted arena receipt)
        | Option.some receipt =>
          YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel (state.enqueued child rest receipt)
'YulangClosure.NativeValueDrain.emit.eq_def' depends on axioms: [propext]
```

### YulangClosure.NativeValueDrain.prepareAll.eq_def

```text
YulangClosure.NativeValueDrain.prepareAll.eq_def : ∀ (x : Nat) (x_1 : YulangClosure.NativeValueDrain.Control),
  YulangClosure.NativeValueDrain.prepareAll x x_1 =
    match x, x_1 with
    | 0, state => if YulangClosure.NativeValueDrain.ready state = Bool.true then Option.some state else Option.none
    | fuel.succ, state =>
      if YulangClosure.NativeValueDrain.ready state = Bool.true then Option.some state
      else (YulangClosure.NativeValueDrain.prepareOne state).bind (YulangClosure.NativeValueDrain.prepareAll fuel)
'YulangClosure.NativeValueDrain.prepareAll.eq_def' depends on axioms: [propext]
```

### _private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_5.eq_2

```text
_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_5.eq_2 : ∀
  (motive : List YulangClosure.NativeValuePorts.Child → Sort u_1) (child : YulangClosure.NativeValuePorts.Child)
  (rest : List YulangClosure.NativeValuePorts.Child) (h_1 : Unit → motive [])
  (h_2 :
    (child : YulangClosure.NativeValuePorts.Child) →
      (rest : List YulangClosure.NativeValuePorts.Child) → motive (child :: rest)),
  (match child :: rest with
    | [] => h_1 ()
    | child :: rest => h_2 child rest) =
    h_2 child rest
'_private.YulangClosure.NativeValueDrain.0.YulangClosure.NativeValueDrain.emit.match_5.eq_2' does not depend on any axioms
```

### YulangClosure.NativeValueDrain.preflight_parent_active

```text
@YulangClosure.NativeValueDrain.preflight_parent_active : ∀ {parent : YulangClosure.NativeValuePorts.Key}
  {origin : YulangClosure.NativeValueDrain.Origin} {fuel : Nat} {prepared : YulangClosure.NativeValueDrain.Control},
  YulangClosure.NativeValueDrain.ParentPresent parent (YulangClosure.NativeValueDrain.start origin) →
    YulangClosure.NativeValueDrain.prepareAll fuel origin.control = Option.some prepared →
      YulangClosure.NativeValueDrain.Active parent
        (YulangClosure.NativeValueDrain.start
          { arena := origin.arena, children := origin.children, control := prepared, tasks := origin.tasks })
'YulangClosure.NativeValueDrain.preflight_parent_active' depends on axioms: [propext, Quot.sound]
```

### YulangClosure.NativeValueDrain.native_drive_constructs_common_run

```text
@YulangClosure.NativeValueDrain.native_drive_constructs_common_run : ∀ {views : Nat → Option (Option Nat)}
  {qv qe : Nat → Nat} {parent : YulangClosure.NativeValuePorts.Key} {post : Nat} {derived : Bool}
  {origin : YulangClosure.NativeValueDrain.Origin} {fuel : Nat} {cursor : YulangClosure.NativeValuePorts.Cursor},
  YulangClosure.NativeValueDrain.Active parent (YulangClosure.NativeValueDrain.start origin) →
    YulangClosure.NativeValuePorts.drive views qv qe parent post derived fuel
          (YulangClosure.NativeValuePorts.initialCursor origin.arena origin.children []) =
        Option.some cursor →
      ∃ state,
        YulangClosure.NativeValueDrain.emit views qv qe parent post derived fuel
              (YulangClosure.NativeValueDrain.start origin) =
            Option.some state ∧
          state.cursor = cursor ∧
            YulangClosure.NativeValueDrain.Run views qv qe parent post derived
                (YulangClosure.NativeValueDrain.start origin) state ∧
              state.cursor.todo = []
'YulangClosure.NativeValueDrain.native_drive_constructs_common_run' depends on axioms: [propext, Quot.sound]
```
