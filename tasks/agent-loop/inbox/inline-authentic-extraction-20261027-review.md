# INLINE-AUTHENTIC-EXTRACTION-20261027/r1 — independent frozen review

Disposition: **FAILED_INCOMPLETE**. Accept the handoffs as an honest incomplete-probe report; reject this candidate as an authentic finite trace or parent-theorem application. All original gates remain **OPEN**. This review admits no r2, separate workspace, additional process budget, or implementation authority.

## Scope and pins

Fresh non-author review. The candidate and its HIR/syntax owners were inspected before using producer explanations to compare the handoffs. No Cargo, build, test, Lean, Lake, Git, or descendant invocation occurred.

Verified SHA-256:

| Frozen input | SHA-256 |
| --- | --- |
| Contract | `015c8c276dde26747b82cea6bf1ff14784a19ced91a8234487cff93c46b09254` |
| Source handoff | `a6b09733222243b779cfb8ed4c2e7ba4da3aa0fc3c765c0bc225ef7852463d30` |
| Proof handoff | `001de7deee35769a92f7beacb12e253443fd74993aa04f327cb8979a996b880f` |
| Rust candidate | `1ab6f3ed86d6bfc6d8f73baa40e5e46d5e3d451922af06fc1092a93ca29a39c0` |

All **28** frozen input pins in the contract matched independently, including the listed HIR/syntax owners, focused inline-lambda tests, runtime owners, manifests and lockfile. The generated trace, proposed extraction theorem module, and extraction audit module are absent.

## Findings

### BLOCKING — binder-token provenance is corrupted inside the extractor

Location: `tools/inference-playground/src/bin/inline_authentic_extraction.rs:74–78`, serialized at lines `164–165`.

The owner supplies distinct Lambda and binder positions, but `inline_origin` constructs `lambda_range.start..binder_range.end`. It consequently serializes the Lambda prefix as part of the binder token.

For the literal input at line `13`, direct ASCII byte counting gives outer binder `12..13` and inner binder `21..22`; the helper instead constructs `11..13` and `20..22`. These are statically derived fixture offsets, not observed runtime values.

The responsible owner already preserves the exact token range at `crates/yu-hir/src/module/local_source.rs:2107–2113`. `crates/yu-hir/src/shadow.rs:1817–1829` selects a unique Identifier token with that range. The extractor introduces the defect after this correct owner query.

Violated contract: fixed outcome lines `14–20` and hard boundary lines `44–47`, requiring an exact binder token and rejection of mismatched ranges before serialization.

Minimum closure: return the binder position’s exact range and authenticate equality with the corresponding `LocalSourceParameter.range` before emission; subsequently obtain and independently review an executed frozen trace under newly granted resources. Merely changing the serialized field name would preserve the cause.

### BLOCKING — raw callee and projected Lambda are conflated

Locations: candidate lines `60–66`, `219–235`, `170–171`, and `180`.

The search strips Group nodes to find the inner Lambda. It retains both indices, but emits `applyCalleeIsInnerLambda = true` without an explicit projection relationship.

`crates/yu-hir/src/module/local_source.rs:2213–2227` constructs a distinct `LocalSourceForm::Group` and inner index for the parenthesized expression. Thus the fixture’s actual Apply callee `(\x -> x)` is a Group; the enclosed Lambda is the result of projection. The current Boolean cannot establish raw constructor or index equality.

Violated contract: lines `16–20` and `44–47`, requiring actual Apply/callee incidence and authenticated joins.

Minimum closure: preserve the raw callee constructor and its complete Group-to-inner incidence, distinguish raw equality from projection, and establish the source projection used by the original-model application. Do not repair this by selecting an unrelated Lambda or replacing the actual argument.

### Major — serialization loses the ordered surrounding body

Locations: candidate lines `145–174`, with internal checks at `241–257`.

The program checks an outer Sequence/StatementBlock and searches its children for the Apply followed by a restored outer Name. It emits selected ordinals, but omits the outer body’s range, constructor, and complete ordered child structure. A consumer cannot independently reconstruct the actual surrounding source body or audit all intervening incidence from these fields.

The owner retains ordered Sequence items at `crates/yu-hir/src/module/local_source.rs:2657–2669` and ordered StatementBlock statements/final expression at `2812–2830`. This is an extraction omission.

Violated contract: fixed outcome’s actual constructor relationships and preservation of identities, together with the proof lane’s requirement to establish nested-shadow/restored-sibling resolution.

Minimum closure: serialize the authenticated outer-body constructor, range, complete ordered incidence and explicit selected positions. Preserve statement distinctions if the constructor is StatementBlock.

### BLOCKING — original allocation and context bridge remains unestablished

Locations: candidate lines `140`, `153–174`, `183–184`; source handoff lines `58–64`; proof handoff lines `125–138`.

The candidate deliberately projects identities to numeric ordinals. No inspected Rust owner connects those projections to original expression/formal/administrative Sites, resolved Names, declaration, root Context, or ambient event telescope.

The distinction is material:

- `SourceNodeKey` equality includes parse allocation, green-node allocation and offset: `crates/yu-syntax/src/full_parse.rs:72–90`.
- `HirParameterId` equality includes its source-root owner: `crates/yu-hir/src/module.rs:1377–1415`.
- LocalSource indices are root-branded: `crates/yu-hir/src/module/local_source.rs:49–60`.
- Runtime labels are authenticated LocalSource offsets plus ordinals: `tools/inference-playground/src/runtime/program.rs:598–603`.
- Runtime Lambda and Apply handling retain captured environments and actual callee/argument fields: `runtime/machine.rs:864–898`, `1181–1195`. These operations supply no original-model allocation equation.

Violated contract: lines `22–29`, explicitly prohibiting adoption of a numeric convention as the allocation law.

Minimum closure: establish the actual owner witness and its allocation equations, including name separation where required, complete outer-body correspondence, declaration/root Context and ambient events. The proof handoff correctly identifies this as a subsequent original-model premise after a corrected executed trace. This review establishes no universal absence theorem about allocators elsewhere in the repository.

## Handoff assessment and execution limits

The source handoff accurately characterizes the three independently verified static defects/omissions and explicitly distinguishes intended checks from execution evidence. The proof handoff preserves that distinction and claims no new checked theorem, printed type, or axiom audit.

The two Cargo failures are **producer-reported execution receipts**, at source-handoff lines `90–100`. They report exit `101` in `yu-solver` before the extractor ran, with allocation failures of `34832` and `1605648` bytes. The proof handoff correctly attributes its knowledge to that report. This review did not rerun commands or inspect raw execution logs, so it does not independently certify those historical process events. The absent generated output is independently confirmed.

Owner inspection supports the intended authentication route: exact parse branding, HIR occurrence/source associations, registered inline binder origins, lexical push/restore, and explicit Apply children. Focused inline-lambda tests encode exact-token and foreign-owner expectations; they were read, not run. `parameter_source_position` intentionally returning `MissingSource` for inline parameters is not a frontend defect.

The identified failures belong to the provisional extractor and its missing bridge. They provide no source-language counterexample and authorize no compiler, parser, HIR, runtime, or semantic change. The candidate is incomplete before the required authentic trace exists; recognizing an allocation frontier does not supply the missing trace or parent application.

## Cessation receipt

Review writes: **none**. Scratch writes: **none**. No compiler/tool files changed. No build, test, checker, Git, or child process was started.

The complete review is returned to the primary for persistence at the leased review path, respecting the reviewer’s read-only instruction. All reviewer activity stops with this receipt.
