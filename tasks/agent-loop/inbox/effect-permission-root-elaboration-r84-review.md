# R84 independent review receipt — revision 1

Reviewer `/root/r83_review`; verdict **PASS for the frozen source and exact
audit assembly**. The reviewer stopped without writes, Lean/compiler/test
execution, scratch, cache, environment, worktree, or descendants.

## Scope and findings

The reviewer independently checked all twenty module pins and import edges,
220 declaration slices, normalized source, contexts, line maps, thirteen full
query pairs, R83 diagnostic headers, contract/manifest/receipt pins, and exact
slot-1 and proposed slot-3 recipes. All matched the frozen records.

The eight R83 audit-2 diagnostics match their retained stdout and source
locations: one R77 `choice_three_premises` invalid simp argument plus its
residual goal, and three invalid/no-progress pairs in R81
`primitive_records_derive_source_probe` at source lines 146, 150, and 154.
Six normalized declarations contain exactly 24 substitutions from bare
`unique` to `YulangClosure.SourceInternalContextR55.unique`; no other source
bytes change. Both definitions are definitionally equal readers. The pinned
Lean simp implementation supports unfolding the fully qualified definitions.

The R84 candidate changes its namespace and qualifies two native `Origin`
types and two native `unique` references. All thirteen theorem signatures are
byte-identical to R83. Original R66 `Root`, `BeforeAncestry`, incidence,
nonempty witness, and rejection claims remain unchanged. No blocking, major,
or minor source finding was reported. The actual elaboration remains untested.

## Frozen input identities

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| Candidate | 22,748 | `1681d78a8ec4b103dac7fb808bc4cdd02e0a46cba196ad5a64db6c10601f1839` |
| Proof handoff | 331,759 | `c9ba9b410094cea83309b2df18e64f42fe4308ef7b158c708fb737d41ead618a` |
| Normalized prefix body | 78,934 | `ee4abd52c66c46bf714ca196be6de1fbb46ee2f2f31e17dd882a9c367b14ab49` |
| Slot 1 exact stdin | 93,368 | `e031132b1a5a42f22c5faba355a1af3d8639d0d577de9051e81f403bf465ebb3` |
| Proposed slot 3 stdin | 103,791 | `5c35dd49b71508fea4755abf680327932099249de1d1f4f5f250ca2d949651f2` |

Slot 3 remains gated on an accepted prefix and a fresh authorization. Prefix
success alone accepts no R84 theorem. Source/native extraction, Rust runtime,
original A/B, and production remain open.

**Disposition:** slot 1 is eligible for Luna's separate exact-input
authorization. This review does not authorize or execute Lean. Reviewer
STOPPED / WRITES STOPPED.

## Slot 3 retained audit review

After slot 3, reviewer `/root/r83_review` independently authenticated the
complete retained result at
`tasks/agent-loop/history/effect-permission-root-elaboration-20261031-r84-slot3-raw-result.json`.
The exact input is 103,791 bytes, SHA-256
`5c35dd49b71508fea4755abf680327932099249de1d1f4f5f250ca2d949651f2`; Lean
exited 1 without timeout in 11.605 seconds. The retained 79,844-byte stdout
hash is `6b7e874b4ff08b5675505d4c2d685fc34d5a320b1eef1fc59f2abf9f254458d4`;
stderr is empty. Raw-result SHA-256 is
`db6ceb58d4fa88755d1b2136cef45ae46af0374e1a870919df361ba8b9ee7d91`.

Nine diagnostics are real blockers: R84 source lines 144, 149, 151, 186, 297,
311, 342, 351, and 355. They include unresolved Origin and candidate-list
proofs; a rejected reverse simp-unfold; an `admission` definitional mismatch;
unresolved `Decidable Primitive` computation at `sorry`; dependent constructor
rewrite/transparency mismatch; two unresolved constructor reductions in
finite rejection computations; and an independent relation-list parser
failure. The reviewer explicitly did not attribute the latter computation
failures to cascading Root errors.

All thirteen type/axiom reports appear. `value_endpoint_typed`,
`effect_endpoint_typed`, `primitive_distinct_relation_roles`,
`constructed_applies_parent`, and `finite_reads` report only `propext` or
`propext, Quot.sound`. Eight reports contain `sorryAx`: both primitive Root
derivations, `finite_primitive`, `finite_constructs_root`,
`finite_nonempty_mixed_witness`, all three rejection theorems. The final
rejection theorem's proposition itself contains `sorryAx` because of parser
recovery. No theorem is accepted from slot 3.

The reviewer found source-only repair targets that preserve all claims and
semantics, but requires the single slot-4 repair to address every blocker,
including the unresolved finite-decider and dependent reduction causes. No
further invocation is authorized by this review. Reviewer STOPPED / WRITES
STOPPED; no edits or execution.

### Primary diagnostic-count correction

Primary rereading of the authenticated complete stdout found an additional
independent diagnostic omitted from the reviewer table: `<stdin>:1833:0`,
candidate source line 126, `lean.synthInstanceFailed` while elaborating the
`Decidable (Primitive ...)` instance. The slot-3 output therefore has **ten**
error headers, not nine. The proof worker traced the missing instance to
`Option (Relation T)` equality in the two `relationRead` equations; pinned R57
`Relation` has no `DecidableEq` deriving clause. The slot-4 source review must
verify the proposed local derived instance and still audit the dependent
finite reductions independently.


## Fresh revision-2 review — 2026-10-31

**PASS for frozen candidate source review and exact slot-4 input. No remaining blocking source finding.** This permits a separate primary authorization; it does not establish kernel acceptance.

Authenticated candidate r2 (22,427 bytes, SHA-256 `5d8ad6429906cdf971dbb9ee44841223c1fcc28e6591e1a75d1f453ea4eac13d`), handoff r2 (339,182 bytes, `8241f3b7ab3a656c15d114a987159fd33c66f04ae48fc3d82dbda0e4972ed17b`), and independently reconstructed slot-4 stdin (103,470 bytes, `93b365ddf908e223558d166efe7f76a1f5c370a5b1c9080716d0fb0ce92b3df0`). The original handoff remains an exact 331,759-byte prefix. All 220 dependency slices, six normalizations, accepted prefix body, and thirteen query pairs are unchanged.

All ten prior diagnostic targets have owning repairs. The tenth tagged `error(lean.synthInstanceFailed)` was omitted by the prior `error:` regex; the structural `DecidableEq` for the local `Relation` addresses the `Option (Relation T)` comparison. Origin filtering is preserved until the pinned equation rewrites it; root-candidate unfolding, guard evidence and `congrArg List.map hcandidates` discharge the actual singleton obligation; admission unfolding addresses the bound mismatch; direct `rfl` replaces the dependent rewrite chain while preserving the constructor/output equality. Closed finite reductions use `decide +kernel`; pinned `Lean/Elab/Tactic/Decide.lean:83–135` distinguishes this from native evaluation and adds no native-evaluation assumption. Parentheses group full relation/origin map expressions without changing intended values or rejection conjuncts.

Twelve theorem signatures are byte-identical. The thirteenth differs only by the grouping parentheses; reversing them recovers the previous source signature. Definitions, primitive checks, inventories, coordinates, witnesses and quantifiers remain unchanged. No proof hole, project axiom or checker bypass appears.

**Gate:** slot 4 must exit 0 and provide all thirteen complete types and axiom reports without error recovery or forbidden axioms. This is the last permitted invocation; any remaining failure closes R84 incomplete.

Reviewer `/root/r83_review` STOPPED / WRITES STOPPED. Read-only review; no Lean/checker/compiler/tests, writes, scratch or Git.
