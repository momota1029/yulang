# LEAN-CALL-LITERAL-RESPONSE-20261025/r1

Status: **AUTHORIZED and frozen by the current user-selected primary.**
Baseline `3a1af4d9c1c31b13d4d6bbc5e12acf3d55b08484`, branch
`research/simple-sub-intrusion`. Original goal: complete Lean proofs of Yulang
semantics/type inference over accepted source/native behavior, preserving all
original Call/inference A/B and arbitrary-suffix quantifiers.

## Exact obstruction, authority and outcome

The preceding source audit (artifact SHA
18519640506d193b75dbeef374e806b6b07e926043cfca3cada02ed43087da57) and fresh CLEAN
review (SHA a7fd56ee2fc51274a4a3c888a3029c1f22d6a4a3c6d1ac38f93f8dfa318ebd26)
identify missing literal values in the formal typed fragment. Raw Literal already
represents eight kinds, but Original.Val represents only unit. Consequently the
closed typed response premise cannot be supplied for actual native int/bool/str
responses at their base types. This is an encoding gap, not a source-safety
counterexample or permission to weaken host/source assumptions.

At the real completion/representation boundary, the existing Astra dispatcher
selected a literal syntax/typing extension and application to the exact actual
request theorem. Both 180-second consultations are charged (360 cumulative),
STOPPED/read-only. No new semantic decision is needed: governing
`docs/yulang-operational-type-safety-ja.tex`:215 already types constants at their
base type. Preserve the parameter domains of existing Original.Literal and its
exact raw atoms. Native lexical validity and full source encoding are not thereby
proved. No runtime/compiler change or broader authority is granted.

Required outcome: every existing literal is constructively represented by a
closed typed value with its unchanged literal datum and base type; typed/raw
substitution and existing raw execution safety retain their original statements;
the constructed response typing is applied to arbitrary actual Call request and
completion prefixes. The theorem must construct `hv`, not take it as a premise.
The formal operation/literal type equality remains explicit. Full source/native
operation, environment, template and trace correspondence, callable responses,
Force realization and original inference A/B remain OPEN.

## Author packet: three stages, Astra/medium, 300 active seconds

1. Preserve legacy `Val.unit`. Add seven matching value constructors for existing
   Literal bool/Int/floatBits/String/bytes/path/char, with exactly their original
   data types. Define total Literal.base and Literal.toVal, choosing unit's
   existing constructor. Add corresponding ValTyped rules. Raw erasure must be
   exactly `.atom (.literal l)`, with no data normalization or type conflation.
   Do not introduce a duplicate `.literal .unit` typed representation.
2. Extend rename/substitute and their typed/raw-commutation proofs. Any
   CoreExecution edit is limited to proof cases needed by this extension; do not
   change RawStep, principal steps, failure rules or existing theorem statements.
   Prove total typed literal construction, exact raw erasure, injectivity of
   Literal.toVal, uniqueness of its base typing, and invariance under arbitrary
   rename/substitution. Place additional public lemmas in CallLiteralResponse.
3. Construct TypedCall.Value.original of the literal, then apply the accepted
   request-boundary/response composition to any actual initial and completed
   request prefix with `op.responseType = .base l.base`. Retain length, exact
   endpoint/head, literal suffix and the typing of captured-response/frame
   plugging. No assumed `hv`, erased value data or native safety claim.

Exact author paths (no directories or additional scratch files):
- `notes/theory/lean/YulangClosure/CoreSyntax.lean`
- `notes/theory/lean/YulangClosure/CoreSubstitution.lean`
- `notes/theory/lean/YulangClosure/CoreExecution.lean`
- `notes/theory/lean/YulangClosure/CallLiteralResponse.lean`
- `tasks/agent-loop/inbox/20261025-call-literal-response.md`

Author is not alone; preserve all other edits. No descendants, Git, Lean/tests/
build/runtime invocations, compiler/config/docs/expectation edits or external
contact. Primary is the one verification owner after STOP. Author supplies a
frozen source candidate/handoff with exact hashes, authorship, parent application,
remaining premises and cessation of writes/subprocesses. A semantic mismatch,
changed unleased input or budget exhaustion returns immediately to primary.

## Primary verification, bounded repair and generated leases

After actual author STOP, primary receives the four Lean source leases and may
make ordinary elaboration/case-proof repairs inside this same scope. Never change
an original theorem's premises/conclusion to get a green check. Freeze final
source after the last repair before independent review.

Rebuild the 28 accepted affected modules plus their two unchanged prerequisites,
and the new module, in dependency order. The four historical failed candidates
CallEntryTyping, CallEntrySpine, CallStepTyping, CallUnwindTyping are explicitly
excluded, not certified; their Repair successors and both entry compositions,
CallProgressObstruction, CoreControlBridge and top-level YulangClosure are included.
The two Force-only modules do not depend on CoreSyntax and are outside this delta.
No stale pre-extension dependent `.olean` may enter final certification.

At most80 serialized Lean calls, each `lake env lean -j1 -M1024`, timeout120 seconds,
aggregate actual Lean time <=240 seconds. Development failures are retained;
repair only within remaining envelope. Final checks include exact public
signatures/axioms, unchanged safety statements, and falsifiers. Record full
source/query/streams, before/after input and imported/output hashes, UTC/monotonic
times, exit/timeout, and fsynced rows. Allowed axiom subset [propext, Quot.sound];
no holes/custom axioms. This is proof verification authorized by the original
goal, not a broad test or compiler execution run.

Exact primary scratch/receipt/outcome paths (review path transfers only to the
fresh nonauthor reviewer after freeze):
- `notes/theory/lean/.lake/call-literal-response-r1-check.lean`
- `notes/theory/lean/.lake/call-literal-response-r1-run.py`
- `tasks/agent-loop/inbox/20261025-call-literal-response-r1-verification.jsonl`
- `tasks/agent-loop/inbox/20261025-call-literal-response-r1-review.md`
- `tasks/agent-loop/sprints/call-literal-response-20261025-r1-outcome.md`

The exact generated paths below are reserved for primary only after author STOP;
they may be activated in a compact hashed bundle referencing this contract. The
bundle must enumerate these exact paths, never imply a wildcard lease. No other
agent may generate them. All are ignored `.lake` outputs, not Git artifacts.

- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/Contracts.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreComposition.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreComposition.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSyntax.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreSubstitution.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreExecution.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreExecution.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlSyntax.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlSyntax.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlTyping.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlComposition.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/ControlComposition.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreControlBridge.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CoreControlBridge.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallResponseCancellation.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallResponseCancellation.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestUnwind.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestUnwind.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureTyping.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureResponse.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallCaptureResponse.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallContextTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallContextTyping.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntryTypingRepair.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntryTypingRepair.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPeelingTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPeelingTyping.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntrySpineComposition.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntrySpineComposition.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntrySpineRepair.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallEntrySpineRepair.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFailureUnwind.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFailureUnwind.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallStepTypingRepair.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallStepTypingRepair.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPrefixTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallPrefixTyping.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallTerminalTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallTerminalTyping.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFiniteTyping.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallFiniteTyping.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallViewedForceReachability.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallViewedForceReachability.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallViewedForceStuck.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallViewedForceStuck.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallProgressObstruction.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallProgressObstruction.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundary.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundary.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallUnwindTypingRepair.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallUnwindTypingRepair.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundaryComposition.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallRequestBoundaryComposition.ilean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallLiteralResponse.olean`
- `notes/theory/lean/.lake/build/lib/lean/YulangClosure/CallLiteralResponse.ilean`

## Independent review, falsifiers and resources

One fresh nonauthor Astra/medium reviewer, <=300 seconds/three stages, after
all source/query/receipt bytes are frozen. Primary and author are ineligible.
Source-first review covers all eight literal cases, exact datum/type/erasure,
mutual substitution arguments, unchanged raw-successor coverage and safety,
actual-prefix response application, final imported/output hashes and axioms.
No review rerun is required; reviewed execution receipts are not an independent
execution claim. Review must be CLEAN before promotion/integration.

Falsifiers: duplicate unit representation, Bool/Int confusion, 11 vs23, negative
integers, empty/Unicode strings, bytes/path confusion, float bit changes, char
payload changes, and response binder shifts under captured bind/adapter frames.
Use both general theorems and explicit kernel examples. Retain original typed
host protocol; do not claim this supplies source callback/environment typing.

Fresh1800-second envelope: author300 + primary600 + Lean240 + reviewer300 +
integration120 + contingency240. User explicitly requires Astra subagents,
overriding default Sol routing for author/reviewer: cumulative600 seconds, one
child at a time, no reset. Three historical UNKNOWN reservations remain
quarantined. Only one Lean process, 1CPU/1GiB, no heavy Cargo/test process.

Implementation lane NO_SAFE_CODE_SLICE: actual machine::primitive_matches/
ResumeArgument and capture_template/enter_template were inspected in the prior
reviewed source audit; the first missing owner is typed representation. No
runtime bug or approved compiler change follows. Primary bridges the literal
construction into the already implemented formal response consumer instead.

Next consultation is at completion, counterexample, material source/authority/
lease/resource change, or a genuine proof obstruction, not each repaired case.
Only primary stages explicit reviewed paths, updates current/outcome, inspects
outbound commits and pushes without forcing. All remaining parents stay explicit.

## Baseline source pins and verification order

The table pins mutable source BEFORE this authorized extension and all immutable
module dependencies. Check the baseline before editing; final hashes belong in
verification/review. New module has no baseline bytes.

| Module in dependency order | Baseline SHA-256 |
|---|---|
| `YulangClosure.Contracts` | `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e` |
| `YulangClosure.CoreComposition` | `1527cd3c5961b413ec2b97495744b218aba6247956881318485364d15065294c` |
| `YulangClosure.CoreSyntax` | `dff3e5851c9ef971ec404f9542d684074a13623bb0820c3a5e4d5da072783ece` |
| `YulangClosure.CoreSubstitution` | `c4bca75be173f20d7a48751205f488ac5f0057b476e6f52d1ef7abcf046a001a` |
| `YulangClosure.CoreExecution` | `86b4bdbf605046d7648fba803aa31eb9e96264627f123f8d14bf937813b4ef7e` |
| `YulangClosure.ControlSyntax` | `1f937e4c51b79d1a2dc4a2291a1e3f5797403eae5975a53a42d574867a1690f0` |
| `YulangClosure.ControlTyping` | `e52aaca8baa5c3312a200952ef07fa7e304686d2642c154831de0365646a497f` |
| `YulangClosure.ControlComposition` | `9a48a5f2ef15eb947478757e0fa74457579183ccdbab90f2518886590e33fc40` |
| `YulangClosure.CoreControlBridge` | `30a0007aea313eccc42531bf346891c010dbed7b4b34cea1aebe7043a9a6d99a` |
| `YulangClosure` | `04a209f4aa4a9e8c2848aee11eb16befb6fe4e0b566d4683dd0705f96ccf3b2f` |
| `YulangClosure.CallResponseCancellation` | `ab9083bab971acd4e72cb8db95d567b309a240e1773b3fc4544fa6968ffe9488` |
| `YulangClosure.CallRequestUnwind` | `e4835bd2c2487b14d658b02373e0507ea6c201b81a1fb81d396b0f05a1850fc9` |
| `YulangClosure.CallCaptureTyping` | `906e8204aa155efd3f4e45d9c2a2a9fbe010858206ef3dd0acfd3d0d607a0de9` |
| `YulangClosure.CallCaptureResponse` | `a310f3da1091a2dd7ed1d751aea67c44aefe06ce89fc9bb16cc0d19b530eb1c6` |
| `YulangClosure.CallContextTyping` | `09bc05fc8561ee81186dd6eae3667a77b0360a8dd27a6236548dfb01d33a5125` |
| `YulangClosure.CallEntryTypingRepair` | `f90c2192422e35cc7f85716e29199c9587976e230e12543aff0609eedcc49c39` |
| `YulangClosure.CallPeelingTyping` | `f89e31759657f602ba69b41a31c9f63ba61f003aa1ebe560323d65dda2b33c44` |
| `YulangClosure.CallEntrySpineComposition` | `a296a5ae738cb3ca8f88a6009495e0fe84a2a394976aafeb4630d6cdd25a11bf` |
| `YulangClosure.CallEntrySpineRepair` | `ad4a2e1b49b13dc71b77b079b80b0c6c6355327915a4be343276b9b9497f7d89` |
| `YulangClosure.CallFailureUnwind` | `2d7422bc4c83310a1a1d0a2bcaa5528bb6a8801520c42db2f2ada6b12224b89c` |
| `YulangClosure.CallStepTypingRepair` | `2ef522c022a0708be670f1ab44b57c8f558d4736f123e14ceb5f6ff259a3c586` |
| `YulangClosure.CallPrefixTyping` | `95c49daec0417c8130a498b44783c546b9464b96380731182fedde5665e8b5bc` |
| `YulangClosure.CallTerminalTyping` | `319466c8276a638166733a28694881e3d980befd5798006ebc984907a8820a6d` |
| `YulangClosure.CallFiniteTyping` | `555e6ee61fad15c93df70bbec13781716d83292a86110a6eb6670018e9b70588` |
| `YulangClosure.CallViewedForceReachability` | `ce6e45da496ceb3f5d7e1150f57ebdf5f62dd0495ee3a8deb1b61035b39cee8c` |
| `YulangClosure.CallViewedForceStuck` | `71164cef48ca86866ef4aae9661ea2e9388e9741062e159a97f3c26b42614ae9` |
| `YulangClosure.CallProgressObstruction` | `8dc8b1b72c952dc45c431fb965a438b700dc86902a68b8d77a3de0b7d47858b7` |
| `YulangClosure.CallRequestBoundary` | `28ffc2943c18d324c35dacf18b4dd70921d4cc462ffd6ffdce989475ef46cce6` |
| `YulangClosure.CallUnwindTypingRepair` | `1eaea1938f6ee2341352afcc597847fc2ade5b8ce8d3be84dda19926fe217cc3` |
| `YulangClosure.CallRequestBoundaryComposition` | `fed00f06cdbf2a5bdc1b3c18957acc33c7b281e890f277ca5bd1d20ece53ee76` |
| `YulangClosure.CallLiteralResponse` | `NEW` |
| `docs/yulang-operational-type-safety-ja.tex` | `a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b` |
| `notes/theory/lean/lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `notes/theory/lean/lakefile.toml` | `2514197994dc47b5e4c6f15ff8c9251f994056b6e32bf2648588ffc10251e194` |
| `notes/theory/lean/lake-manifest.json` | `058325944d936e85c1f601e68f3147f790dbbd0d0286357949466ce1ad3504c3` |
