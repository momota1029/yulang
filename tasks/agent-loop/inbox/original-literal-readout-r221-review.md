# R221 fresh independent review

Verdict: **PASS for the bounded obstruction report; 0 BLOCKING, 0 major, 0 minor submission findings.** The frozen inputs do not construct the requested original literal readout. **Parent-premise delta remains 0.** This accepts the contract's obstruction stop, not a proof of impossibility, a semantic counterexample, model admission, or parent closure.

Reviewer: `/root/r221_review`, independent of the producer and falsifier; no coauthors or descendants. Baseline supplied by primary: `yulang3/d39ec2532e424526d8808dc6fd4ba13b95113766`. Exact lease: this file only. Requested/observed model and effort: UNKNOWN/UNKNOWN; no authenticated runtime metadata used. Frozen producer: `R221-ORIGINAL-LITERAL-READOUT/r1`.

## Cause and ownership

The cause is the absent admitted source-to-solution interpretation at the model/generator owner. It is not a failure of R220 atom rigidity. The submission correctly stops at that owner and does not hide the missing equation in a downstream `LiteralAtom`, `Satisfies`, or assumed readout law. Nothing in the inspected definitions repairs that cause; the submission accurately describes an unconstructed interface.

The decisive source facts below were checked directly in the definitions. Producer and falsifier prose was treated as a submission to audit, not evidence of those facts. The producer note was initially read with the contract; its claims were subsequently checked against the owning definitions before adjudication. This is documentary/source review, not independent checker execution.

## Exact source-to-consumer analysis

1. **Original source and generated clauses.** `OriginalSourceSyntax.lean:40–49` and `PaperExecutionSyntax.lean:20–28,576–584` support the eight payload carriers and type map. `OriginalSourceGeneration.lean:85–89` preserves the entire literal in its declaration atom and retains the site/context. Its `Build:870–871` compiles the source rule tree; `Satisfies:842–864` interprets local clauses through the supplied kernel. The reconstruction theorem at `1019–1031` relates that formula satisfaction to the same source-rule judgment. It does not turn regular graph-store satisfaction into source satisfaction.

2. **Graph outward construction.** `AbstractGeneratorDenotationR220.lean:31–36,116–122` takes caller-supplied variable coordinates and a store-fragment satisfaction premise. Its conclusion is exactly the two node lookups at the same `refs`: the constructor atom and effect bottom. `SimpleSubRegularPublication.lean:12,16–20,44–47,65–86` decodes into `Option Nat`; variables retain their assigned reference and atoms use an existing equal node. No original Descriptor/Value/Root/Event codomain or source endpoint allocation occurs there. The actual generated literal's variable allocation and fragment inclusion must still come from the generator owner.

3. **Required original projection.** `OriginalSourceInterpretation.lean:830–850` has independent endpoint maps for descriptor/value/root; `SourceAssignment.row` reads all three at `⟨site,finalRoot⟩` and retains exactly the supplied event. `Sorts:23–50` supplies types, and `Inputs:324–371` supplies ground/value-form/trace-form relations. Neither is a graph decoder. `LiteralAtom` additionally consumes the original declaration, `.ground` descriptor form, and ground row. Thus the same graph solution has not yet been identified with an original assignment whose consumed row realizes L1's descriptor/value/root/event tuple.

4. **Original frames inward construction.** `OriginalSourceEnvironment.lean:239–245,308–320` starts with a supplied `SourceAssignment`. Logical frames at `346–352` install supplied descriptors and update eta/witness; object/runtime frames at `360–380` install supplied values/roots and update actual event data through the supplied runtime readout (`286–306`). These updates are not a graph-to-source interpretation and do not automatically preserve every original event coordinate. `foldedLiteralKernel:963–970` still requires `LiteralAtom` for its decoded assignment; `folded_generated_literal_membership:981–1002` extracts already-present form/ground facts. Both construction directions leave the same equation open.

5. **Pure Return is a separate consumer boundary.** `TraceForm:308–310` in `OriginalSourceInterpretation.lean` has `.pureReturn (value : ValueRow s)`. `return_observation_iff:680–689` assumes that trace-form equation and retains coherence, observation guards, world membership, event equality and positive observation fields. `generated_name_return:972–990` likewise takes Return form and world/guard premises explicitly. An effect graph node `.bottom` constructs none of the required trace/interface/incidence data. L1's pure `Comp(empty,τ(l))` Return remains to be realized with the original value/root/event and enclosing obligations.

6. **Literal consumer and parent quantifiers.** `generated_literal_membership:896–913` takes source-formula satisfaction under `literalKernel`; it extracts the form and ground facts and uses `GroundLaw`/`ground_membership:805–826`. Heredity propagates an existing ground fact to compatible events; it does not establish the initial literal declaration or row identity. Its conclusion is value membership, not the original full source witness and same-solution `sameScoped`. `Contracts.lean:128–130` still universally quantifies the actual solved `a` and requires one source witness related to that very `a`. No submitted theorem removes this premise, establishes the Return projection, or supplies the joint witness.

## Edge and sibling attacks

- Distinct `.int 0`/`.int 1` share atom code 2; recovering their payload from that code fails. This does not refute an interpretation that also consumes the original literal, which R220 retains. Bool, floatBits, strings, bytes, paths and characters have the same separation. The note preserves that distinction.
- Duplicate equal graph nodes permit node equality without reference-index identity. Replacing the assigned reference by `findNode`'s first result is unjustified; R220 correctly promises lookup equality only. A future interpretation could be invariant under duplicate nodes, but that invariant has not been supplied.
- `OriginalSourceSyntax.lean:359–368` declares synthesis, finalRoot and writtenTarget separately. The annotation rule at `OriginalSourceGeneration.lean:35–43` connects synthesis to writtenTarget. Equal solved types do not establish endpoint equality. The submission correctly avoids requiring every converted final descriptor to equal the intrinsic descriptor; the actual conversion and the literal rule's consumed row must be reconciled.
- `A.row` preserves `A.event` definitionally, but that is not an equation identifying it with the original `(e₀,ξ,ω)` of the same solution. Runtime/logical updates make the missing provenance consequential. A replacement assignment or independent existential witness would not satisfy the parent.
- Taking free `declarations := fun _ _ => False` makes the generic `LiteralAtom` impossible while leaving R220 unchanged. This is a valid interface-separation argument only. It is not an authentic L1 model or source-qualified counterexample, exactly as the producer states.
- `OriginalCheckingAdmission.lean:643–674` explicitly limits its Bool sorts to admission plumbing. Reusing it as a complete all-payload semantic instance would erase information and change meaning. Neither submission does so.

No AST/CST, Rust/native, error recovery, or mutable compiler state change is delivered. No inference about those routes follows from this review.

## Authority, evidence class, and adjudication required

L1 “Adopted introduction” fixes the sufficient intrinsic rule and original coordinates; “Proof and implementation boundary” expressly leaves generation, satisfaction, readout, model realization and `sameScoped` open. The contextual interpretation's §3 also retains foreign descriptor/interface embedding obligations. The frozen report respects both and does not reopen L1 or narrow independently admitted checking alternatives. R203/R205 are historical source-owner context; their former unadopted literal choice cannot override L1.

**Remaining gate blocker, not a defect hidden in this submission:** the source model/generator owner (Luna with the independent generator/solution model owner) must supply an admitted carrier interpretation and actual endpoint allocation. Minimum closure evidence is a constructive same-solution equation at the literal rule's consumed finalRoot row, carrying complete payload and original `(q,r,e₀,ξ,ω)`, deriving declaration/form/groundness, realizing pure Return and conversion boundaries, and applying it to the unchanged parent witness. A new wrapper with these conclusions as assumptions does not close it.

Primary adjudication is required to accept the bounded `NO_ADMITTED_CARRIER_INTERPRETATION` result, keep the original parent OPEN with delta 0, and resolve that exact model input before another solver-reflection packet. The report does not justify a new semantic decision, global absence claim, or production change.

There is no new Lean declaration/type or axiom audit in R221. The exact R220 type was independently inspected in source; its prior complete `[propext]` audits for all six declarations are inherited from the authenticated R220 outcome, not rerun here. No tests, Lean/Lake/build/cache, Rust, Git, network, new environment, scratch file, or subprocess worker ran. No executable counterexample is claimed. These omissions match the assigned read-only review scope.

## Input authentication

SHA-256 was computed from all read input files below. Contract/direct semantic pins match the frozen contract and handoffs. `current.json` is a scheduling snapshot only; its hash is not a frozen semantic dependency or proof evidence.

```text
4a6c910e12adb8f5ccc07b0921f2cc781ea7044994f99425d3c54c4e75837d3c  AGENTS.md
99ae7bbda0a8907a48f762420d996e145e9870ad9794ea0dc608770131182882  AGENTS.pre-sprint.md
e4055100f6e75b9c8a6294ec6c68643d8677d7b35b45e430450f7e2c2ad97eb1  rules/design-authority.md
db55dfb7568805ac6b6372fe8bc05cc00731ae5b5ed33c6af72007a7ce885810  /home/momota1029/.codex/skills/yulang-proofs/SKILL.md
0f829876325565f3c42fbf1950d01deef8c6fda4e92989f668ce1adada41efd6  tasks/agent-loop/README.md
ed52e0aa579f5da72c71759adfdc029d1c60ab0411e61b226eeaeba85780edfd  tasks/agent-loop/current.json
bdaa51efd7aecb2a0e291e256cec4749fc0ad78ca0623e4b1cc7b08bf8a49876  tasks/agent-loop/sprints/original-literal-readout-r221.md
1d4f46b9e9d2375d31284957c4157906df9fd00477fc976d43204262dedcb805  notes/theory/2026-11-02-original-literal-readout-r221.md
3da0827d4c71ade065b33660ea3d8b2ba355374674b4bda537bcc02f10dcf25c  tasks/agent-loop/inbox/original-literal-readout-r221-proof.md
f06751e46d07cd50b43df3605c93d716d725f1483a233777f8099563d26ae444  tasks/agent-loop/inbox/original-literal-readout-r221-falsifier.md
f69a11121b0bade01586293fbda5500c4264424c3ac568fd1336ebb1b2eec9b8  notes/design/2026-11-02-literal-l1-adoption.md
bbd73afe54030cf3e4378a379a58a6836da1b44c9fd227b0bb8b372329f8a254  notes/theory/lean/YulangClosure/AbstractGeneratorDenotationR220.lean
feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef  notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean
126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef  notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean
3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1  notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean
d0dc9871c382ca945059167b8b9e05f8f672170208a994f081e29760a207b87d  notes/theory/lean/YulangClosure/PaperExecutionSyntax.lean
2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e  notes/theory/lean/YulangClosure/Contracts.lean
0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132  notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean
18fc6f138204e1529dcd0bb9c01a20de7444a26e4dadc87677460ccd8ac9fc99  notes/theory/lean/YulangClosure/SimpleSubRegularPublication.lean
77a8dd74f5913814d3628f0aed189be24b4aafc4780839eaa57237676a157da7  notes/theory/lean/YulangClosure/OriginalCheckingAdmission.lean
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
d17f2c1f40e1e2d7c092add2a972ed5c84af50d58e33b81db685aac103fb4bb1  tasks/agent-loop/history/r203-outcome.md
9047ffe6fae59bd1d6e51609e87f2f4c8ac8752d659218f5a7039bdb83199fc7  tasks/agent-loop/history/r205-outcome.md
eac0414232cd2afa93b2a10e7f2a6280db6e3489d026baccdb69dca3305c940a  tasks/agent-loop/history/20261102-abstract-generator-denotation-r220-outcome.md
```

Checks: focused `cat`, `sed`, `rg`, SHA-256 and tool-clock reads; decisive definitions reread in bounded output after a scheduling/governance batch was truncated. The source/dependency envelope is explicitly bounded; unnamed equivalent constructions elsewhere are not ruled out. Budget: below 600 seconds; no heavy process or descendants. Only the exact leased review file was written; unrelated shared work was preserved.

**WRITES_STOPPED**: review revision 1 frozen. No further writes in this assignment. Primary owns all adjudication, records, integration, and Git.
