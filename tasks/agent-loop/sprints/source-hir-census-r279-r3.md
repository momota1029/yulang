# R279-r3 — fixed-source HIR census complete-helper extension

Status: CANDIDATE until the targeted r3 integrity/owner gate, separate
derivation GO, and independent review complete. R3 versions only the evidence
view and remaining resource split. The 87-byte source, census claim, source
domain, semantic authority, and production authority remain unchanged.

## Objective and falsifier

For this exact input:

    my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }

classify the result from production source equations as one of:

- `SOURCE_PIPELINE_ROUTE_EXCLUSION`: every normal successful parse/HIR return
  for this source has a top-level Binding count other than two;
- `COUNTERCASE_TO_CENSUS`: a permitted path, including a recovery-bearing
  path, normally returns `Ok(hir)` with exactly two top-level Bindings;
- `UNRESOLVED`: an owner or source-to-census edge remains uncovered.

The countercase is decisive. Diagnostics or recoveries are not implicit
failures. An `Err`/panic edge excludes only the paths that reach it; every
other normal `Ok(hir)` route must be accounted for.

The reviewed R278 premise is conditional: `assemble` filters `hir.items()` to
Bindings and returns `CandidateError::Unsupported` unless the count is exactly
two and the original items contain no Expression. Thus a proved count-not-two
invariant for this source implies exclusion at that guard only. It proves no
observed call, same-HIR identity, later guard success, ordinary-source result,
global unreachability, accepted-source counterexample, or theorem closure.

## Preserved dependencies and r1/r2 decisions

R278 contract SHA-256:
`26281ae2d1b6dafda3acd8b6b16a38d6541729512a14ba93b5b85777e6761233`.
R278 theory SHA-256:
`bc6876084151d872c08f565bd0a0bf79173e1c7902da683c811b9b44dd20b82e`.
R278 review SHA-256:
`7a67c5e08cd671e9588a07abe75e8e501185568dac0f64fb8a565bdbddbc6f5f`.

R279-r1 contract SHA-256:
`b946d87a15bb9c232597585821221b605c1e9a2bfe2794e4680f7238d825d6a2`.
R1 stage-1 STOP SHA-256:
`3c51593c20207fafe4087a4995b1502a4d4ddeb78b95fd7ee51c4ba3811b2824`.
R1's reported 181,149-byte prose count is a clerical typo; its authenticated
index/STOP establish 181,148 bytes. Integrity passed. R1 contract, view,
ranges, index, admission and STOP remain unchanged.

R279-r2 contract SHA-256:
`f9f9973939f11a5f683bc1a465aaeddbb5733cdeb25ee8f5e4ec889d0c2455c2`.
R2 stage-1 STOP SHA-256:
`370b834dbd9b7fa22e927d9ac65a70f0ee1e7e7b257ee709e4ef31d6f2a9cd78`.
R2 independently passed integrity for 229 inventory paths and 46 payloads,
then stopped INCOMPLETE because E044 ended at the declaration of
`structural_diagnostic::byte_range`; its body at lines 512–513 was outside the
view. R2 also flagged the open `use_tree_starter_source` declaration at
line 1735. No census derivation occurred. R2 contract/view/index and STOP stay
unchanged.

The source inventory remains
`tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`,
SHA-256 `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f`;
all admitted source paths must be among its 229 entries.

R3 exact source artifacts:

- ranges `tasks/agent-loop/sprints/source-hir-census-r279-r3-ranges.json`,
  SHA-256 `b56e41c85a479c3191cf6c8bc2f1e9194313aa74c804a3ab67975c4c55f899a3`;
- view `tasks/agent-loop/sprints/source-hir-census-r279-r3-source-view.txt`,
  SHA-256 `1c4f7bbc6b873f873cb50025d6f5c58cf37307ebb505efdc8f6d8e60dbec118b`;
- index `tasks/agent-loop/sprints/source-hir-census-r279-r3-view-index.json`,
  SHA-256 `ef01d9f0ba95effb7ecc79d80301ac972e74774f98b6fe62e85b9738deedcc30`.

R3 has 49 indexed payloads over 21 inventory paths and 247,489 bytes. It
preserves all 46 r2 payloads and the entire r2 view as an unchanged byte prefix,
then appends three production payloads with new IDs:

- R279-R3-E047: `structural_diagnostic.rs:511–513`, complete
  `byte_range` definition;
- R279-R3-E048: `use_decl.rs:1735–1740`, complete
  `use_tree_starter_source` definition;
- R279-R3-E049: `use_decl.rs:1808–1816`, complete `version_starter` and
  `use_identifier_spelling` definitions.

The final two are needed together: `use_tree_starter_source` calls
`source_identifier` (fully included in the r1 payloads) and
`use_identifier_spelling`; the latter calls `version_starter`. `byte_range`
uses `TextRange::start/end` and infallible `usize::from` conversions. Its body
has no explicit error or branch. No external/library source body is admitted;
the proof may rely only on the in-scope API operations needed to state its
returned half-open byte range, and must not infer exact runtime behavior beyond
that boundary.

No admitted production interval contains `#[cfg(test)]` or a `#[test]` marker.
The old fixture-only R279-E001 remains isolated, is not evidence, and must not
be rendered or inspected by Sol or the reviewer. No source body outside an
exact indexed interval may be opened. All helper bodies claimed below must map
to a complete indexed definition or an explicit source-grounded branch
exclusion; a signature, re-export, path, or digest alone is insufficient.

## Five-edge helper-closure table

This is the required owner map for the bounded gate, not a census conclusion.
Sol must verify complete definitions, call edges and normal returns from the
indexed bytes. A further omission is INCOMPLETE and requires a fresh exact
extension; do not infer that this list is exhaustive merely from these rows.

| Edge | Complete indexed path | Required normal-return account |
|---|---|---|
| Header item advance | R279-E015 → E028 re-export → E029 `next_use_item_lex` → E011 `current_item`, E030 payload scanner, E004/E005/E013 trivia scanners, E003 cursor, E006 `scan_identifier`, E008 identifier-start, E009 identifier-continuation | Exact item, consumed offset, line state and normal return. For this fixed prefix, `scan_version_token` fails at `m`, then `scan_identifier` consumes `my`; later `scan_use_payload` alternatives are unreachable. |
| Header use selection | E015 → E032 selected normalized/lexical/prefixed decision → E013 trivia, E007–E009 identifier helpers, E031/R3-E048 tree starter, R3-E049 identifier/version helpers | Exact Boolean and header continuation/stop for this input; every advertised helper body is complete. `use_tree_starter_source` is reached only if its preceding source-head checks pass. |
| Effective operators | E014 parse entry → E033 effective merge/error mapping; E034/E035 conversion; E036–E041 operator table/default/builder; E042 imported-only syntax environment | Account for imported/local declarations, duplicate handling, builder failures, `Result`/`expect`, and the actual table passed to root parsing. Do not assume empty/default operators. |
| Structural recovery projection | E014 `ParsedFile::try_structural_recoveries` → E043/E044 `try_collect`/walk/classification → R3-E047 `byte_range` | Account for Missing/RawError/Invalid enumeration, byte-range conversion, ordinal exhaustion, invariant failure, and every returned projection. Do not assume empty diagnostics. |
| HIR recovery acceptance | E024 HIR lowering → E046 `validated_recoveries`/ErrorSink; E045 recovery partition/emission/attachment; E022/E023 HIR shape/items | Account for which recovered parses return `Err`, which attach errors to module/root/definition/value, and which recovery-bearing paths still return `Ok(hir)` and their Binding count. |

For each edge, name any directly called nonstandard helper and map its full
definition to an ID above. Standard API use does not grant external source
reads. Use only exact-source facts to exclude an unreachable branch.

The derivation then justifies:

`fixed source → header/root parse and recoveries → returned ParsedFile → HIR
lowering/recovery handling → returned HirModule.items() → Binding count`.

## Stages, leases and fixed resource envelope

Producer: stopped Sol `/root/sol_r274_source_acceptance`, requested
`gpt-6-sol/high`. R1 gate charged 200 seconds and r2 gate charged 200 seconds;
Sol cumulative charge before r3 is 11,800 seconds. The remaining unissued 800
seconds are split without refund, reset, or extra allocation:

| Component | Seconds | State and gate |
|---|---:|---|
| R1 owner gate | 200 | Charged; INCOMPLETE |
| R2 owner gate | 200 | Charged; INCOMPLETE |
| R3 integrity/helper-closure gate | 100 | Charge at GO; fresh contract/admission, WAITING, Luna pin check, separate resume; no census or outputs |
| R3 census derivation | 700 | Separate GO only after READY; fresh resume; exact output pair below |
| Fresh independent review | 900 | After producer freeze; full source-to-census/recovery/guard review |
| Luna preparation/adjudication | 300 | Exact views, gates, review adjudication and records |
| **Total** | **2,400** | No extension or reset |

R3's first gate reauthenticates the 229-row inventory, all 49 payloads, every
whole-file/source interval/hash/byte length/offset/bound/nonoverlap relation,
and the r2 prefix; then checks every row in the five-edge helper-closure table.
It returns READY or exact INCOMPLETE. It is not a census proof. Cumulative Sol
charge becomes 11,900 seconds when the 100-second gate is issued. If coverage
is incomplete, stop before spending the 700-second derivation allocation.

Only after READY may Luna issue a separate 700-second derivation GO. Cumulative
Sol charge becomes 12,600 seconds. Sol must return
`SOURCE_PIPELINE_ROUTE_EXCLUSION`, `COUNTERCASE_TO_CENSUS`, or `UNRESOLVED`,
including all normal and recovery-bearing `Ok(hir)` returns. A permitted
two-Binding return falsifies the proposed census invariant.

Only during that proof stage, exact output leases may be granted after
absence/lease checks:

- `notes/theory/2026-11-03-source-hir-census-r279.md`
- `tasks/agent-loop/inbox/source-hir-census-r279.md`

No other write path. No tests, builds, probes, Cargo, Lean, runtime execution,
code edits, broad/caller searches, fixture substitution, generated/scratch/cache
outputs, external paths, semantic changes, or descendants. Sol may read only
the exact indexed source intervals plus required pinned records.

After a coherent frozen producer result, a fresh independent referee gets 900
seconds and no write lease. Review must independently reconstruct the complete
source-to-census implication, recovery propagation and application of R278's
guard. Repeating only the conditional guard check is insufficient. The
reviewer also must not inspect tests or R279-E001. No review stage begins on an
INCOMPLETE producer packet.

## Parent status

This packet is witness-local and cannot close the unchanged theorem. Parent/A/B
remains **0→0**; `Need_D`, R70/R71, accepted-source soundness, F1/FK1, foreign
continuations and full production closure remain **OPEN**. There is no safe
implementation slice (`NO_SAFE_CODE_SLICE`).
