# R119 first-method post-adoption implementation packet

Status: candidate planning artifact; **NO_SAFE_CODE_SLICE while R85 remains unadopted**.
Sprint: method-role-producer-feasibility-20261019-r119, contract rev2,
SHA-256 6639951a68a8248c705e5df8c954488ae782e8ffb0fbf8639fb821c4326bed58.
Baseline: af551a720. This packet specifies a future owner-by-owner vertical path
for the exact R85 fixture. It is not code/test authority, semantic adoption,
proof closure, production approval, or permission to alter current inference.

## Fixed source and required result

    role SecondInt {
        my second: int -> int -> int
    }
    impl int: SecondInt {
        my second self selected = selected
    }
    my answer = SecondInt::second 1 2

The post-adoption first public observation is a successful stdin run of the
yu-playground binary with --run answer --steps 100000 -. It must return exit
status 0, stdout exactly 2 followed by LF, and empty stderr. The argument order
in the source is significant: resolve the member head first, then ordinary
receiver 1, then ordinary argument 2. The source call is represented as
Apply(Apply(C_member, E_receiver), E_argument). No special method evaluator or
signature-derived executable role is part of this packet.

The R85 positive offer at notes/design/2026-10-19-r85-role-call-positive-contract.md
is Draft and unadopted. It is the only proposed semantic decision surface. Its
exact adoption by the user, after the required independent reviews, is a hard
prerequisite. The packet does not decide general lookup, ambiguity, mismatch
classification, diagnostics, dot dispatch, adapters, or other method forms.
For this one fixture, the required positive InterfaceMatch, ordinary
CheckedBody, and unique authentic ValidatedTarget remain separate gates.

## Current owner facts and vertical contract

| Owner | Current pinned behavior | Exact post-adoption owner work and retained data | Falsifier / gate |
|---|---|---|---|
| Parser source and yu-hir shadow source projection | The parsed tree contains RoleDeclaration, ImplDeclaration, a nested member BindingStatement, and the qualified call syntax. ShadowArtifact can retain exact raw Role/Impl positions and source keys; its pending role/impl sources explicitly are not semantic IDs or a selection rule. Existing Apply source projection recognizes ordinary CallTail and MlArgument forms. | Preserve the one-parse SourceNodeKey for the role declaration, implementation declaration, member header, each binder pattern, body name, qualified member head, receiver, argument, and each Apply occurrence. Associate positions with their authentic constructors; never infer member identity from spelling or parser association alone. | Missing, duplicate, foreign-parse, or conflated keys; parser association treated as semantic selection; a source Apply omitted or assigned to a different operand. |
| yu-hir module producer and identities | Production plan_root admits direct BindingStatement and OperatorChain roots. A standalone ImplDeclaration becomes UnsupportedItem; lower_plan emits HirItem::Error before it creates a member DefinitionRootId, parameter IDs, body, or lexical environment. The carrier pass skips Error items. plain_binding_header handles ordinary binding forms, and its production flags do not admit this multi-tail member header. SourceRootId currently has Definition and Expression variants; HirItem has Binding, Expression, and Error. | After adoption, add an authentic implementation/member HIR owner rooted in the actual ImplDeclaration/member BindingStatement. Mint distinct role, implementation, and member identities tied to their declaration source owners and the adopted exact target relation. Preserve the member body as an owned root, the ordered executable binder vector self then selected, each binder's own optional annotation and IdentifierPattern origin, and the actual body IdentifierExpression origin. Do not publish a fabricated top-level Binding or bind the member by bare spelling. Keep error/recovery and availability gates explicit. | An existing authentic producer for this exact member would falsify the bounded R112 obstruction and must be reported. Also falsifying: substituted top-level binding, synthetic binder, dropped/reordered binder or annotation, body resolved by spelling rather than lexical identity, or selection without adopted authority. |
| yu-hir LocalSource construction and call formation | form_ordinary runs only after admission. form accepts Binding or DirectExpression plans; it zips supplied HIR parameters with admitted header parameters, parses annotations from each original binder syntax, creates nested Lambda nodes in order, and resolves Name through its active lexical scope. Its resolution and root variants currently have no implementation-member target. | Carry the authentic member root and parameter IDs into LocalSource without reconstructing them from text. For this fixture the nested Lambda order is self then selected; both original annotations are absent, so both executable roles remain Value under charter §21. Retain their source keys, ranges, IDs, lexical scopes and body occurrence. Resolve the original body name to the selected parameter ID. Resolve SecondInt::second to the adopted authentic member target, then form the two ordinary Apply nodes with preserved source forms and child occurrences. Do not read role-signature slots to choose executable binder roles. | Any body name that resolves to a module binding instead of the second binder; any role inferred from signature rather than the binder's own annotation; missing root ownership; no exact source origin; or a special call node that bypasses ordinary Apply. |
| yu-solver candidate source and admission | emit_candidate_source requires pointer identity with the HIR-owned LocalSource and checks that its SourceReceiver is an admitted Definition record or matching Expression root. It registers Lambda formals by HirParameterId and their own annotations, maps parameter names by ID, and creates ordinary candidate recipes/actions. Existing source construction does not admit a member root/target. | Admit the authentic member root and target metadata through the same ordinary candidate pipeline. Register both binder IDs and preserve their annotations/roles; resolve the member head to its exact candidate endpoint. Generate the ordinary nested Apply constraints for member closure, receiver, and argument, and run existing candidate conflict/preflight/admission over the complete module. Keep InterfaceMatch, CheckedBody, and ValidatedTarget distinguishable; no shortcut may suppress ordinary endpoint conflicts or withhold required candidate metadata. | Candidate accepts a spelling-only or partial target, skips body constraints, changes operand order, suppresses an ordinary conflict, admits an incomplete source root, or publishes despite a missing InterfaceMatch/CheckedBody/ValidatedTarget premise. |
| RuntimeProgram publication and existing machine | RuntimeProgram::from_hir currently consumes Binding, Expression, and a narrow Error case, fetches each retained LocalSource, emits Lambda, Name, and Apply instructions, and indexes top-level Definitions. It creates source execution roots separately from the code labels. Its LocalSource resolutions contain no selected role-member identity. | Publish the member's code/root and authentic target identity in a callable member table consumed by an ordinary Name/Apply path. Preserve source root, occurrence and byte range for the member body and all call nodes; retain the actual parameter IDs and annotation-derived Value roles. Keep the member callable but do not add it as a fabricated top-level CLI definition or an extra module execution root. The ordinary machine applies the selected closure to 1 and then 2. | Runtime target cannot be joined to the HIR member identity, runtime republishes a different body/binder vector, method becomes an unrelated top-level definition, source provenance is lost, or execution returns another value/stream. |
| Public CLI entry | main.rs accepts --run answer, --steps N, and stdin path -. It reads source and calls yu_playground::execute. execute calls prepare; prepare parses/lowers one HIR and solves candidate inference from its clone; execute then passes that same HIR to RuntimeProgram::from_hir and prints the completed integer plus LF. | After all prior gates and independent review, observe the exact source through the public binary using --run answer --steps 100000 -. Require status success, stdout exactly 2 followed by LF, stderr empty. Keep this as the first public observation; do not substitute direct RuntimeProgram construction or a unit helper for it. | Candidate failure, runtime unavailability, noncompletion, a result other than 2, extra/missing stdout bytes, or any stderr. A passing observation is finite executable evidence only, not proof of R85 or the original evaluator theorem. |

## Prerequisites and owner seams

1. User adopts the exact R85 offer hash
   fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609,
   with the offer's positive InterfaceMatch and separate CheckedBody and
   ValidatedTarget boundaries. A clean review alone does not satisfy adoption.
2. The authentic member producer resolves the source declaration/member
   relation and owns the body root, exact ordered binders, their original
   annotations and lexical environment. R112's bounded missing-producer
   premise remains open until this output exists.
3. Ordinary body checking validates selected = selected against the declared
   int result and effect obligations. No signature-derived binder, fake
   top-level binding, parser-only association, or weaker ordinary inference
   can stand in for this premise.
4. The selected member head resolves to that exact validated target, and
   receiver-first lowering retains whole operands and exact origins as ordinary
   nested Apply. Candidate inference must admit the complete HIR and all
   generated constraints without a side channel or suppression.
5. RuntimeProgram publishes the same HIR-owned target metadata and ordinary
   instruction graph. Only then may Luna authorize the first CLI observation
   under a separately frozen verification contract.

Owner-local future changes are expected in the HIR source projection and module
root/member producer, LocalSource identity/resolution/call formation,
candidate-source collection/admission, RuntimeProgram publication, and the
public execution path only where a new target lookup requires it. This list is
a review seam, not a current write lease. Any needed owner outside the R119
inspect set, any new semantic choice, or any dependency drift returns to Luna
before a future implementation packet.

## Evidence reused, rejected, and remaining

Reused within reviewed finite scope:
- R108 exact-source entry identifies the distinct ImplDeclaration,
  BindingStatement, self/selected IdentifierPattern nodes, and selected body
  IdentifierExpression.
- R100 constructor-to-consumer derivation shows conditionally how authentic
  binder IDs, annotations, body, and environment can flow through LocalSource,
  candidate parameter registration, and RuntimeProgram consumers. It does not
  supply the member producer.
- R112's reviewed bounded obstruction shows this exact ImplDeclaration stops
  before member root, binder, body, and environment creation.
- R116's conditional bridge provides the downstream role-preservation path
  only after its producer and successful-consumer premises hold.
- R85 supplies an unadopted positive offer and the exact separation among
  InterfaceMatch, CheckedBody, and ValidatedTarget.

Rejected or not used as authority: the R84 handoff claim excluded by R100's
provenance audit; the R85 offer as present semantics; an assumption that the
source already executes to 2; and any synthetic Binding or withdrawn shortcut
around normal candidate admission. R100, R112, and R116 do not close P1/P2/P3/P4,
R85 adoption, R100-P2, R117-JOIN-1, the six effect fronts, method/role proof,
the original evaluator, or Simple-sub A/B.

## Direct pins and frozen boundary

Contract-provided direct source pins: module.rs
153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907;
module/local_source.rs
3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786;
source_identity.rs
7f0ba057a28ec8c42d2b08bcbe698ee9b422819bfde8ea43ce184457ea586bb3;
candidate_source.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c;
RuntimeProgram program.rs
c2363ad42104b895519bb29a8eb9aeda545bd0176cebbd78750d3a2df90849ca.
The implementation inspection also read the contract-authorized shadow source
and CLI entry owners. The contract and source text were read; no hash/check
command was run under this assignment's no-commands rule.

No code/test edits or executable verification were performed. No semantic
expectations, diagnostics, source domains, production settings, or questions
were changed. Fresh independent compiler/source and specification reviews are
required on these frozen artifacts; the author cannot certify them. Next step
is Luna review/intake and, only after an explicit user adoption event, a new
implementation lease.
