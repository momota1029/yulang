# Nested odd/even: current source owners and occurrence-record seam

Status: frozen bounded source characterization; `spec_auditor` and
`compiler_referee` PASS
Baseline: `fd94dedee30c06f83a3a867ea8da413d3b688eab`
Branch: `research/simple-sub-intrusion`
Method: read-only parser/CST/HIR/candidate producer and consumer audit
Lease: this file only; no implementation, test, build, delegation or Git authority

## Objective and fixed authority

The assigned exact text is:

```yu
my odd n = my even n = if n <= 0 { true } else odd(n - 1); even(n - 1)
```

This is the one-line spelling in the assignment. The previous
[source-admission audit](2026-10-12-odd-even-source-admission-audit.md) investigated
the separate indented spelling with a newline after `my odd n =` and a nested
statement sequence. Neither spelling is replaced here by a brace-block program.
No parser run establishes the actual CST of either spelling in this packet.

Authority is fixed by the top-level inference principles §§1–3 and “Authority
and integration”; parent-copy SCC intrusion, “Value-reference SCC clarification”,
“Apply-result source-fragment ownership”, “Nested Apply membership” and
“Definition-root Value ownership”; value-to-type association, “Approved
extrusion-event qualification”, “Definition-root origin for nested call-demand
extrusion” and “Implementation and proof boundary”. The approved nested-origin
answer revision 1 and its integrated receipt supply the accepted decision,
including wrapper-nested calls. They do not authorize production implementation.

Under that selected source meaning, let O and E be the original resolved odd
and even definition roots. The inner odd call is owned by E; the final even
call is owned by O. Definition-root incidence gives `E -> O` and `O -> E`.
The inner call-demand extrusion has origin E and resolved receiving callee O.
Its actual retained pairs qualify for intrusion when that approved graph is
constructed. `C=T` and `D=R` denote the pairs in the approved derivation; this
audit does not claim that current Yulang emits those exact type coordinates.
Levels and subtype judgments are not Value-reference edges. The two formal
Names spelled n denote different lexical binders. No permanent Value owner is
assigned to every Function port or to a type row.

## Exact spelling: first unavailable constructor

All source locators below are repository-relative and use the pinned baseline.

1. `crates/yu-syntax/src/statement.rs:453` selects Binding at a statement entry;
   `declaration/binding.rs:185` constructs BindingStatement/Header/Body.
2. With no newline after the outer equals, `binding_body_normalized` at
   `declaration/binding.rs:317` chooses its inline expression branch at `:350`.
   `inline_binding_body_normalized` at `:365` calls expression parsing at `:392`.
   It does not call the statement-family selector for a nested declaration.
3. Ordinary expression scanning at `lexical/lexer.rs:89` recognizes the contextual
   expression words if/case/catch through `:705`, then operators or ordinary
   tokens. The separate statement-keyword scanner includes my at `:711`.
   `scan_identifier` at `:685` returns Identifier. In the ordinary identifier
   route, `expression/operator_chain.rs:303` emits IdentifierExpression; there
   is no my-to-BindingStatement branch in the inspected `append_nud` constructor.
   With ordinary token selection, the inner my therefore starts an expression
   Name, rather than the nested even declaration required by the example.
4. If the ordinary equals reaches a chain tail, `operator_chain.rs:580–590`
   dispatches AssignmentTail. This is not the BindingStatement constructor.
   `module/local_source.rs:519` accepts only ML/Call/colon application tails
   after handling ascription, so an assignment tail cannot repair the missing
   nested binding carrier.

The first unavailable operation on this inspected inline path is **formation
of the nested even BindingStatement/local declaration inside the outer inline
BindingBody**. This is a current constructor limit, not a rejection of the
user-selected language meaning. The conditional token trace assumes ordinary
selection for my and equals; this packet supplies no custom operator environment
or rule expansion that changes their CST. It establishes neither recovery-free
parsing nor an absence theorem over every possible syntax environment.

For the earlier indented spelling, the grammar instead selects
IndentedStatementBlock (`binding.rs:328`, `statement.rs:474`). Its previously
identified carrier cut remains present: `module/local_source.rs:251` requires
the BindingBody's sole child to be OperatorChain, while ordinary lowering
`module.rs:1597` explicitly turns IndentedStatementBlock into an error body.
These are distinct cuts; the inline result is not another run of the previous
indented-body attack.

Even if an authentic nested declaration carrier were supplied, the current
LocalSource enum at `module/local_source.rs:107` has no If constructor, its
expression dispatch rejects unhandled shapes at `:694`, and its chain-tail
filter at `:519` has no InfixOperatorUse case. The expression parser does have
an if owner (`operator_chain.rs:285`). The selected operator environment and
resolved meanings of <=, -, and true were not supplied or executed here.
The lexer retains ordinary true as a Name; its spelling alone is no Bool
literal license. These further cuts do not decide the language's Bool or
operator semantics.

## Actual identity producers, conditional on a supported carrier

The following constructors exist but are not reached for the exact text by an
established end-to-end path in this audit.

| Required information | Actual producer | What it establishes |
| --- | --- | --- |
| Module odd binder | `module.rs:1322` namespace construction, before `lower_root`; parameter IDs at `:1398` | An unshadowed retained odd Name can resolve to the module DefId. Namespace identity is not yet a semantic Value-reference edge. |
| Local even binder and initializer boundary | `module/local_source.rs:729–812` creates HirLocalId, LocalInitializer scope, initializer index and parameter-owner records | Separate local declaration identity survives inside the outer artifact. HirLocalId.owner names the containing artifact; it does not make O the source owner of E's initializer. |
| Shadowed inner n and later even | `local_source.rs:330–383` temporarily installs local self and formals, then restores and publishes the local binder; lookup at `:633` checks latest lexical entries before module namespace | Supported local initializers can distinguish inner and outer n and preserve resolved even for the final expression. No allocated exact-program IDs were observed. |
| Apply occurrence | `local_source.rs:554–593` retains callee/argument indexes and source form; `candidate_source.rs:394–410` retains Apply recipe and checking occurrence | Authentic source fragments can remain linked to candidate demand construction. An Apply type result is not established as a semantic Value vertex by its ComponentKind::Value tag. |
| Definition uses | `candidate_source.rs:376–378` emits PendingDefinitionUse with the containing parent ordinal; local Name actions at `:381–389` use local slots/open initializers | Module scheduling dependencies and local lookup are retained. Neither is an emitted O/E semantic Value graph. |

In particular, `ApplySourceInput` (`candidate_call.rs:29–47`) carries the
outer `DefinitionRootId`, expression/callee/argument positions, typed endpoints,
checking cause, and optional native interface. Its `owner` is set to
`source.definition_root()` at `candidate_source.rs:402`, including calls in
nested local initializers. The existing LocalInitializer/HirLocalId evidence
can distinguish the source declaration, but that outer owner field alone
cannot authenticate E as the approved inner call's extrusion origin.

The approved graph derivation has exactly the premise that the source Names
resolve to O and E and their own definitions own those references. From the
two authentic incidences, the paths `O -> E` and `E -> O` place O and E in one
SCC, without a level test. This is a conditional application of selected source
rules, not observation of current graph emission. This audit does not extend
Apply membership through the still-unspecified Lambda/Block/operator wrapper
boundaries or infer edges to synthetic returned providers.

## Demand, extrusion, publication and fresh use

`shadow_apply.rs:1335–1392` prepares the candidate Apply comparison: it reads
callee/argument/result endpoints, creates a negative four-port Function demand
at `:1366`, and retains `NativeInterface` at `:1382`. The ensuing comparison at
`:1404` enters the live constraint dispatcher. The row/structural branch in
`lib.rs:12433` negatively extrudes an upper description to the receiving type
row's level. These are actual candidate operations, not complete original Call
formation or a derivation of the exact <=/subtraction/if source.

At `candidate_extrusion.rs:22`, extrusion receives only initial typed endpoint,
polarity and target level. It memoizes by those typed coordinates. At `:114–121`
it creates a high-level row's actual fresh copy and calls
`retain_extrusion_parent`. `candidate_intrusion.rs:171–217` stores actual
parent/copy typed rows with polarity and target. `Parent` at `:23` has no
extrusion-occurrence identity, semantic origin Value or receiving Value.
Thus the precise missing certificate is at **Apply demand's source ownership
entering extrusion and its actual pair creation**. Recording a checking
HirOccurrenceId elsewhere does not establish that each copied pair belongs to
that source event, especially after memoization/replay.

The consumer still uses a different graph: `candidate_intrusion.rs:377–472`
enumerates typed Value/Effect endpoints, bound rows, structured descriptions
and Function children. `:477–486` compares component IDs of copy and parent
type rows directly. This is bounded code evidence of the mismatch already
recorded by governing authority; it is not the approved origin/receiver test.
No reversed bound, inferred subtype edge, added copy vertex, or level rank
supplies the missing semantic Value graph.

Publication is separately owned. `candidate_source.rs:300–330` ends active
local initializers and schedules Install at the outer boundary; `:624–651`
uses the PublishLocal stage. `candidate_scheme.rs:1320–1334` installs
`LocalScheme { id, root, boundary }`. A later local Name captures the current
root and prepares fresh use at `:1373–1374`; `:1013` allocates new rows only
for still-local coordinates above the boundary that are not non-generic,
sharing canonical rows otherwise. The captured Graph at `:36–47` contains
type nodes, bounds and contextual evidence, rather than the approved semantic
Value graph and extrusion-event endpoints. Freshening that graph is not an
extrusion occurrence and supplies no new parent certificate. No transport
proof for approved event identity, E/O endpoints or source-owned references
through publication/fresh use follows from these constructors.

The private entrypoint `CandidateInference::solve` at `shadow_apply.rs:79`
preflights LocalSource when available, then selects candidate collection at
`:110`. Ordinary `ConstraintBatch::collect` at `lib.rs:893` selects the
noncandidate route. Neither inspected entrypoint reconstructs the missing
nested/conditional/infix carrier from the exact text. No public typing or
successful exact-source result is established.

## Evidence limits and next action

Claim class: bounded source characterization plus the explicit conditional
source-incidence derivation above; unreviewed. There is no minimized semantic
counterexample or executable acceptance/refusal result. Static source inspection
is independent of the prover's transition derivation, but shares the pinned
Authority and baseline. It does not independently validate those source rules
or prove soundness/principality. No reference oracle, seed/range, mutations or
search enumeration applies; no checker was authored.

Checks: bounded rg/cat/sed reads; read-only HEAD/branch/status queries; Python
SHA256 and byte equality against `git show BASELINE:PATH` for all 21 dependencies
below, with 21 MATCH and zero changes. Initial guessed paths
`yu-hir/src/local_source.rs`, `yu-hir/src/shadow/local_source.rs`, and syntax
`expression.rs`/`lexical/token.rs` did not exist; inspection was redirected to
the real files. No compiler/parser/test/build/format process ran. Reads were
single lightweight shell processes; numeric RSS and total wall time were not
measured. No parallel compute or Git mutation occurred.

Omitted: actual parser environment/CST, exact source admission and typed
primitive/conditional constructors, whole original Call interfaces, generated
C/T and D/R identities, qualified-equality preservation, publication validity,
combined algorithm termination, production correspondence and F5 cutover.
An undiscovered source route or changed direct dependency invalidates any
broader reading of this bounded inventory.

One recommended next action: assign the source-construction owner a bounded
authority-governed bridge for this exact nested definition/conditional/operator
source, retaining LocalInitializer ownership and the approved semantic roots
before forwarding call-demand origin/receiver identity to extrusion pair
creation. Keep the transport and preservation gates OPEN. The absent carrier
must be resolved at its owner; another abstract event/SCC toy cannot establish
that first source premise.

## Frozen dependency SHA256

Every file below is byte-equal to the pinned baseline. Paths use repository roots.

| Path | SHA256 |
| --- | --- |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| `notes/design/2026-10-10-parent-copy-scc-intrusion.md` | `6e9c5fd89655a791b7863c7541465e7e95a52f12417344917b8b48bf93b0a60b` |
| `notes/design/2026-10-12-intrusion-value-type-association.md` | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| `questions/2026-10-12-nested-extrusion-origin-value/approved-answer.md` | `eaa2b19ea059a3aa0fdc5feac40e198b4bc6ee6ef1c5f1bf1fdf3d5381be16ba` |
| `questions/2026-10-12-nested-extrusion-origin-value/receipt.md` | `35e70fcaff0181dfe129200623b3b5111553998834acbe50d0eaeb95e46ded2e` |
| `notes/progress/2026-10-12-odd-even-source-admission-audit.md` | `2bb4b6a1389dc054f6a16a1bf566b68cba7648cd31355a4b10c29b1f91d2cb06` |
| `notes/progress/2026-10-12-odd-even-native-extrusion-audit.md` | `9c44f9220a43631b7bb7e6723b5f777c3f467242e68ff2dcbb19df73e846cec0` |
| `crates/yu-syntax/src/declaration/binding.rs` | `eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544` |
| `crates/yu-syntax/src/expression/operator_chain.rs` | `cd7b6ccd9e0bf92d90de5a0e9e5cfdede5f38990bacb12d60fff8e9fdf8edc2d` |
| `crates/yu-syntax/src/lexical/lexer.rs` | `9a18b24628844e2e5ab1bcc1dc26e05cb14bdb6fca35a3a2d31f45ba5180b3a1` |
| `crates/yu-syntax/src/statement.rs` | `dc18a26663b4351b774a930bfcc8b343cf0c41651960b49ec2f2c6e744b0e89d` |
| `crates/yu-hir/src/module.rs` | `943dcab6440ffb70061f08641afa13fa8b36c5689a326d07288b9593e17ba8f5` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `crates/yu-hir/src/shadow.rs` | `687b49061273974fe874a8479a8db91ba24cc77fe92e6d2b96ae46a3626cf9dc` |
| `crates/yu-solver/src/lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `crates/yu-solver/src/candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `crates/yu-solver/src/candidate_call.rs` | `79ca6f226f91109ea43bf7f794211d5b8f1371c2afbd8bbc94d3c823e7c3ba35` |
| `crates/yu-solver/src/shadow_apply.rs` | `cbd2e0c49a3f1fbe3c5fc78a06d469faedf4aa261525b24a0c9584e9956c2411` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `crates/yu-solver/src/candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-13-nested-odd-even-source-owner-audit.md`.
- Baseline SHA: `fd94dedee30c06f83a3a867ea8da413d3b688eab`.
- Changed dependency hashes: none; snapshot above contains 21 matches.
- Review status: frozen artifact; independent `spec_auditor` and
  `compiler_referee` PASS in their bounded scopes. No language rejection,
  theorem closure or implementation closure claimed.
- Checks already run: source reads, branch/HEAD/status, dependency SHA256 and
  baseline byte equality. Final artifact integrity check/hash is in the report.
- Proposed commit message: `research: audit nested odd-even source and extrusion owners`.
- Shared-record deltas left to primary/curator: cite the exact inline carrier
  cut separately from the previous indented cut; record the nested local origin
  evidence lost at ApplySourceInput-to-extrusion and the current type-row SCC
  mismatch. Keep source admission, occurrence transport, preservation, complete
  Call and F5 gates OPEN; do not supersede approved language meaning.
