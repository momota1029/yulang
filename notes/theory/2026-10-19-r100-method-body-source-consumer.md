# R100 exact member constructor and consumer boundary

Status: **candidate source evidence and conditional constructor derivation**;
fresh independent review pending. Sole author: `/root/r100_member_proof`.
No descendants or coauthors. Assignment `R100-MEMBER-PROOF`, revision 1.
Governing sprint: revision 6,
`tasks/agent-loop/sprints/method-body-source-consumer-20261019-r100-rev6.md`,
SHA-256 `d595f4878b9f931214e5da0cba6d7e53cf3e2e0ca243ecad784e55cac1611dec`.

## Parent application and exact limit

The parent is R85's original P2/P3/P4 source obligation, as stated in
`notes/theory/2026-10-19-r85-role-call-preservation.md` §2–3: P2 retains the
selected authentic member's original executable binders, annotations, body and
lexical environment; P3 emits the same member in receiver-first ordinary
`Apply(Apply(C_member,E_receiver),E_argument)` with whole operands and source
provenance; P4 admits complete candidate/root/target metadata before publication.
R85's semantic decision remains **Draft and unadopted**.

This audit supplies two useful results: (1) an owner-local derivation of the
implementation member's ordered syntax, conditional on entry to the inspected
constructors; (2) an exhaustive branch argument that the inspected HIR path
does not materialize that member from a RoleDeclaration/ImplDeclaration root.
It also identifies the independent qualified-call and runtime admission gaps.
It does **not** certify that `parse_file` actually dispatches the exact complete
fixture into those constructors. Its call to `cursor::parse_root` is visible at
`full_parse.rs:331`; the defining root dispatcher is outside the final pins and
was not inspected. This is the precise remaining source premise `R100-ENTRY`.
No guessed parser dump or test of assumed transitions replaces it.

The parent therefore stays OPEN. Original Simple-sub/evaluator A/B, accepted
source domain and universal quantifiers remain unchanged; F1 and FK1 remain
independent, including foreign continuations. No provider, residual, receiver,
annotation or witness lineage is identified with another. Generation,
accumulation, propagation, levels, extrusion, qualifying intrusion and
generalization remain required. R50 stays NOT_ADOPTED.

## Exact source and constructor derivation

Use the exact seven-line LF source in the sprint contract. Byte coordinates
below count its ASCII bytes from zero, with no initial newline. A final LF
after the last line does not affect these coordinates. These coordinates are
source-byte arithmetic and constructor-derived ranges, **not observed parser
output**. Let `P` be the resulting immutable parse, if `R100-ENTRY` establishes
its authentic constructor entry and successful diagnostic-free publication.

`role_declaration_normalized` starts RoleDeclaration, emits RoleKw, parses its
head, and its LBrace body branch calls the canonical braced statement parser
(`role_decl.rs:189–272,309–362`). `impl_declaration_normalized` starts
ImplDeclaration and calls `impl_tail_normalized` (`impl_decl.rs:168–215`). The
same-line colon selects ImplDescription; it contains Colon and the required
description type; after it closes, the LBrace body branch calls
`braced_statement_block_normalized` (`impl_tail.rs:175–207,234–306,307–411`).
`type_expr/mod.rs:2594–2609` preserves the VARIANT_BODY brace boundary after
an existing head. The special fresh-primary brace policy is not permission to
absorb a brace following an already parsed `SecondInt` as the member body.

The braced constructor starts BracedStatementBlockExpression and emits the
opening brace, then emits the initial newline/indentation before its first
Statement (`statement.rs:578–628`). Canonical Statement surrounds the
selected BindingStatement (`statement.rs:145–176,332–347`). For this member,
the actual nested ownership, ignoring trivia tokens only in this display, is:

```text
ImplDeclaration
  BracedStatementBlockExpression
    Statement
      BindingStatement
        BindingHeader
          MyKw
          Pattern
            IdentifierPattern(Identifier second)
            PatternMlApplicationTail
              Pattern
                IdentifierPattern(Identifier self)
            PatternMlApplicationTail
              Pattern
                IdentifierPattern(Identifier selected)
          Equals
        BindingBody
          OperatorChain
            IdentifierExpression(Identifier selected)
```

This display follows the inspected constructors, under their entry premise.
`binding.rs:185–254` opens BindingStatement/BindingHeader, emits visibility,
parses the target with PATTERN_STOP_EQUALS, emits Equals, closes the header,
then opens BindingBody. `binding_target_normalized` emits the space preceding
`second` before opening Pattern. The Pattern constructor's Identifier branch
emits one IdentifierPattern (`pattern/mod.rs:338–373,764–783`). At Lowest
precedence, ordinary same-line spaces and identifier primaries select the ML
tail branch (`1192–1241`). It emits that space **before** opening the tail and
recurses at MlApplication precedence. The strict comparison prevents that
recursive argument from absorbing the next argument; its returned item is
revisited at the original precedence (`1407–1455`). Thus `self` and the first
`selected` are separate, ordered sibling tails. Equals stops the Pattern;
no annotation is inserted. These are syntax patterns, not yet executable
HirParameterIds or checked receiver/formal roles.

The inline body branch emits the space after Equals before starting its
OperatorChain (`binding.rs:317–425`). `append_nud` selects the Identifier
branch (`expression/operator_chain.rs:302–322`);
`emit_identifier_core` opens IdentifierExpression and emits Identifier
(`cursor/recovery/emit.rs:205–213`). The following RBrace is handed to the
braced owner; it is not part of the body name. The role signature takes the
same binding-header route with a PatternTypeAnnotation, but absence of Equals
closes BindingStatement without constructing BindingBody (`binding.rs:229–234`).
No executable implementation body is inferred from that signature.

| Exact implementation occurrence | Constructor-derived range | Identity/ownership |
| --- | --- | --- |
| member BindingStatement / BindingHeader | `78..112` / `78..103` | actual Statement child / its first node child |
| target Pattern / head IdentifierPattern `second` | `81..101` / `81..87` | header target / target's first node child |
| first tail, its Pattern, IdentifierPattern `self` | each `88..92` | target's first ML tail, then nested children |
| second tail, its Pattern, IdentifierPattern `selected` | each `93..101` | target's second ML tail, then nested children |
| Equals token | `102..103` | BindingHeader token after target |
| BindingBody / body OperatorChain | `103..112` / `104..112` | second BindingStatement node child / body child |
| body IdentifierExpression / Identifier `selected` | each `104..112` | chain child / its token child |
| role header's Identifier `second` | `24..30` | a different declaration occurrence |
| qualified-call member Identifier `second` | `138..144` | PathTail token, a third occurrence |

The two Identifier `selected` tokens have different ranges, node kinds and
parents. The body occurrence is not proved resolved to the formal merely by
equal spelling. Raw child ordinals include all whitespace and newline tokens;
the display's node-only ordering must not be reused as raw ordinals.

For each actual node N, its key is exactly `K_P(N)`, minted by
`P.source_root()` and `SourceNode::children()` descent (`full_parse.rs:69–138`).
Key equality uses the parse Arc, green allocation and start offset. No opaque
key value or numeric PositionId is fabricated here. Tokens have retained
PositionIds but no SourceNodeKey of their own. Their actual node parent's
children and token range identify the occurrence. Authentic parse entry and
actual minted keys remain part of `R100-ENTRY`, not results of byte arithmetic.

## Retention and association preserve syntax, not an executable member

For any successfully constructed diagnostic-free ShadowArtifact A from its own
P, `ShadowArtifact::retain` (`shadow.rs:1198–1273`) proves the following by
induction on its explicit work stack. It starts with the root, pops one raw
element, records exact kind/range/node-vs-token/parent/ordinal, appends the new
PositionId to the parent's children, then pushes all actual children in reverse
order. Consequently traversal is preorder, every original child is retained
once, and children recover the exact raw order. All syntax is visited,
including member body/name patterns beneath an implementation. The temporary
selected-kind map is not the complete retention inventory. Position identity
uses A's Arc and index. Node keys join through P; duplicated keys are marked
ambiguous and rejected by `source_position`. Successful artifact retention is
conditional on the existing depth/element preflight and empty diagnostics.

`pending_role_impl_sources` (`919–928`) lists retained RoleDeclaration and
standalone ImplDeclaration occurrences in that order. The complete
`with_associated_method_role_sources` branch (`931–1049`) checks same-P keys,
round trips and kinds, and publishes borrowed original declaration nodes only
after validation. Its role view is just source occurrence plus SyntaxNode. It
does not enumerate semantic members, mint a RoleId, or form a closure. In this
fixture there is no FieldTail: `::second` is a PathTail. The field inventory's
association-root selection therefore does not associate the call merely
because it contains a qualifier. Do not call that absent field association an
associated role call.

Separately, if an authentic call OperatorChain is passed to the generic
association constructor, `ChainParser::expression` and
`structural_continuation` (`lib.rs:334–405,506–546`) repeatedly prepend the
previous associated value/provenance as child zero for PathTail and MlArgument.
For the inspected path constructor, `fixed_access.rs:182–237` starts PathTail,
emits ColonColon and the accepted Identifier segment, and resumes tail scanning.
The ML constructor (`operator_chain.rs:785–825`) emits argument-leading trivia
before each MlArgument and parses the argument with MlMode::None. Hence the
constructor law gives nested structural Values for the qualified head and two
arguments in source order. It gives no selected executable member and no
semantic `ResolvedExpr::Apply` by itself. R95's distinction between receiver HIR
span and provenance node range is preserved; no whitespace trimming or
range-based identity is used.

## Exhaustive inspected consumer cut

| Layer / complete owner branch | What it constructs; exact boundary |
| --- | --- |
| `module::lower_module_with_counters:1153–1361`, `plan_root:1976–2025`, `namespace:2027–2050` | Plans only direct root children. OperatorChain is DirectExpression; BindingStatement with admitted header is Binding; every other node kind is UnsupportedItem. Namespace receives Binding plans only. For RoleDeclaration/ImplDeclaration root input, no traversal of the member occurs and no member DefId is minted. |
| `module::lower_plan:2052–2204` | Unsupported immediately emits HirItem::Error. Only Binding mints HirParameters, records their source keys, calls LocalSource formation, pushes lexical parameters, lowers the body and wraps Lambdas. Its entire alternate branch has been inspected; it does not convert the retained role view into a member. This is the first missing **executable-member constructor**, conditional on the root shape. |
| `shadow.rs:69–145,624–686` | Captured-source helpers first use the same lowering and require existing HirItem::Binding; the role/impl error fails that route. Declaration skeleton fallback scans direct BindingStatement children only. Source retention supplies no bypass. |
| `local_source::form:556–643`, `Builder::expression:848–1090` | Formation requires an admitted Binding or DirectExpression and rejects Unsupported. Existing admitted named formals become ordered Lambdas, preserving each original annotation and lexical binding; IdentifierExpression resolves through that lexical table. Those operations are unreachable for this nested member through the inspected root route. Its body `selected` has no demonstrated executable environment. |
| `module::lower_ordinary_admission:1421–1502` | Exhaustive projection admits only childless identifiers/integers, unary parentheses and two-child MlArgument/CallTail Values. PathTail returns None. Thus generic structural association cannot silently become an ordinary qualified-member Apply here. |
| `local_source::Builder::expression:848–1090`, `resolve_operation:1091–1103` | Reverse tail construction can retain two ordinary LocalSource Apply nodes with `1` as inner argument and `2` as outer argument. But an initial PathTail becomes Operation, resolved exclusively through effect_namespace/operation_namespace. This is an effect-operation head, not `C_member`. P3's role-target premise is still missing even when the Apply skeleton is retained. |
| `candidate_source::preflight:451–504`, `emit_candidate_source:826–912,1258–1368` | Preflight refuses unresolved/ambiguous Name and non-resolved Operation. Emission requires pointer-identical LocalSource owned by the exact HIR root, authentic occurrence ownership, and original Lambda parameters. Apply records actual operand/effect/result endpoints, cause, level and source owner, then schedules Action::Candidate; it does not reconstruct an impl member from text. No constraints for this member body follow from retained CST alone. |
| `RuntimeProgram::from_hir:249–301,477–538` | Exhaustive item branch admits Binding/Expression roots with LocalSource, and skips only registered effect-declaration placeholder errors. Other errors return MissingSource. Lambdas retain original parameter annotations; Apply becomes ordinary Instruction::Apply. Neither step produces a missing member or admits role/impl errors. No role admission exemption is established. |

The search for role/impl bridge names across these pinned HIR, candidate and
runtime owners found only the shadow bridge definition/use inside shadow.rs.
This is a claim about the **inspected bounded path**, not an uninspected
repository-wide absence theorem. Effect namespace registration internals,
candidate admission entrypoints outside candidate_source.rs, machine execution,
native residual consumers and the root parser definition were not read. The
existing effect resolution branch cannot be relabeled as role resolution to
avoid those missing owners.

## Reuse, exact TODOs and falsifiers

R93's paired constructor/identity argument is reused within successful
same-parse retention/association hypotheses; its candidate status is retained.
R95's closeout is reused only as reviewed bounded source-bridge evidence and
its corrected range law, with its three passing tests historical and not rerun.
R85's finite role-preservation result remains conditional on actual executable
binders. Its proposed result and hypothetical ordinary transitions are not
evidence that these constructors emit a member closure. No standalone
same-spelled binding, R84 total classifier, withdrawn early-satisfiability
bypass or unrelated Act placeholder exemption is imported.

| Stable TODO / owner | Required input, output and exact falsifier |
| --- | --- |
| `R100-ENTRY` / Luna to lease the defining `cursor::parse_root` owner | Input: exact LF fixture, current parse_file and pinned local constructors. Output: source-constructor entry/dispatch proof and actual root/occurrence publication, including raw ranges/keys and diagnostics premise. Falsifier: actual dispatcher does not enter these owners, produces different wrappers/order/ranges, or refuses the fixture. This input is outside R100 rev6; no further inspection is authorized here. |
| `R100-P2-MEMBER` / future approved HIR member-materialization owner (`module::plan_root`, `lower_plan`, LocalSource formation) | After adoption and authentic role/impl identity evidence, retain the exact nested BindingStatement, original self/selected binders, their own annotations, actual body Name and lexical environment. Output must authenticate source occurrences through HIR/LocalSource. Falsifier: today's complete branch already emits that exact member, or proposed materialization substitutes a standalone binder, inherits roles from the signature, or resolves the body by spelling without environment ownership. No code TODO is approved for implementation now. |
| `R100-P3-TARGET` / future approved qualified-call and ordinary admission owner | Input: approved unique target plus P2's member. Output: two ordinary receiver-first Apply edges for that member and whole caller operands with provenance. Falsifier: a separately proved existing path already consumes this exact member; a continued Operation head, reordered operands or a synthetic foreign member fails the proposed result. |
| `R100-P4-ADMIT` / candidate and RuntimeProgram owners under a future lease | Input: authentic target/root/body/graph and ordinary endpoint/body constraints. Output: complete ordinary generation, accumulation/propagation and admission before publication. Falsifier: unregistered role/impl errors or incomplete metadata are accepted; a signature endpoint is copied without ordinary constraints; an Act exemption substitutes for target validation. |

These are requests for evidence, not new semantics, granted leases or permission
to edit production. The next action in this envelope is freeze and stop. Luna
owns fresh review and the explicit adoption/implementation boundary. R100
changes method from assumed runtime transitions to constructor/consumer case
analysis; it does not rename the unchanged P2–P4 assumptions as solved lemmas.

## Frozen inputs, checks and writer receipt

All 28 input rows in the revision-6 dependency table were SHA-256 checked
against their exact listed values across the revision-4, revision-5 and
revision-6 read grants. The immutable manifest is the revision-6 contract at
the hash above. Direct result dependencies include every listed compiler
source except `expression/lambda.rs` and `lexical/expression_item.rs`, whose
hashes were checked but whose implementation bodies were not used. The R85
proof, handoff and sprint locator were read as canonical obligations; they add
no authority. The pinned R93 proof author is `/root/r93_proof_r1`; R85 proof
and handoff author `/root/r85_positive_proof`; R85 proposed decision and R95
closeout are Luna's receipts. Compiler source author identities are UNKNOWN;
this author claims no authorship of their bytes.

Key direct evidence hashes:

```text
R85 decision fee3feaec5e8873fe4f056df3a9ae9ca16c342f0a8b314c027a35719eedd4609
R85 proof    92d207aecb043c102409c543758213511c9843c9302e09fcc415c76fb6fea259
R93 proof    6d3a4d0357f99fa9f1b6978bd66d6210409a6e95a1fe046a53239a09f82e012c
R95 closeout dfdf5272569db6c41e5b19f817b0f1cb39b35dac185fa2459edc7844d4b8cdf1
shadow.rs    9f7a80055076a01cbd99a3eb9c5bc8c3f0db512f2e84032a53af0eacdad2375b
module.rs    c40ebde1755d300c83aafba0a81a85d19ed5200dfc2163ab72c8a3bb08baf29a
local_source 3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786
candidate    66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c
runtime      484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11
binding.rs   eb9b7c9b97b999d16b364531fdcfad0bfc0cb377855e86ce6d5b825f5aba3544
pattern      1b608422c93ce0f6947125a9b1ea88314a48b3a5e45030ed23e5154492ad7883
emit.rs      de091c117486f7990dc6872bf2ee7659c0e3e7e148e255f47b56b7836fe7c59d
fixed_access 9e88d7ce18d8bd2d3c3bfa6fbdd6cac7e37032a21fedc35774c71597ff7a21bd
```

Checks were read-only cat/sed/rg/sha256sum and source branch induction only;
no tests, builds, formatter, compiler/runtime command, Git, external contact,
production/test edit or executable probe. No descendant was spawned. Before
the reviewed inspection clarification, reads/writes were held as instructed;
later added pins were read only after Luna's CLEAN revision receipts. Requested
model/effort: Sol/high; observed model/effort: UNKNOWN/UNKNOWN. First clock
receipt: `2026-10-19 05:21:18 UTC`; final pre-write receipt:
`2026-10-19 05:26:36 UTC`. Pre-clock duration and CPU/memory are UNKNOWN.
The original 900-second grant is cumulative and unexpanded; no exact remaining
time is invented. No independent certification is claimed.

Only this note and `tasks/agent-loop/inbox/20261019-r100-proof.md` are new paths.
No scratch/generated path or descendant lease exists. **STOP at handoff freeze:
writes cease, and review/integration/shared-state ownership returns to Luna.**
