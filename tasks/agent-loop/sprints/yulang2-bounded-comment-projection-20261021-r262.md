# R262 — bounded comment projection feasibility for pinned Y2 sources

Status: ACTIVE primary-only investigation; read-only compiler semantics.
Branch / baseline: `research/simple-sub-intrusion` / `4b27a20aa`.
Authority: unchanged user goal for the pinned Yulang2 Types/Console samples;
R149 and R261. No R168 implementation gate or parent proof gate is closed.

## Original outcome and success evidence

Continue the unchanged Types/Console samples through ordinary tests and
proof-backed execution. This sprint only decides whether a narrow byte-length
preserving projection of the exact pinned library's Y2 `--` line comments to
the Y3 lexer's `//` comments can yield a useful parsed-root witness. It cannot
establish module registration or runtime publication by itself.

Success evidence: authenticate the embedded 40-file source blobs; enumerate
every `--` occurrence with its line and lexical context; transform only
line-leading comments; parse all 40 projected files; check syntax diagnostics,
structural recovery, byte spans and direct root kinds; compare declaration
counts with R260's census. A changed code line, structural error, unmatched
source form or root-count discrepancy falsifies the proposed projection.

## Scope and lanes

Primary proof/source lane only. Inspect `tools/inference-playground/
pinned_stdlib.{rs,bin}`, `crates/yu-syntax/src/lexical/lexer.rs`, and the public
`yu_syntax::parse_file` diagnostics/recovery interface. A temporary local test
probe may be used and must be removed after evidence capture. No production
code, retained tests, sample bytes, expected output, solver behavior or parser
semantics may change. Do not read or write outside this repository.

R260's source census, R259 sample-root derivation, and R154/R149 constructor
evidence are reuse inputs only within their recorded premises. The current Y3
parser is not presumed to be the Y2 parser. The temporary projection is not
accepted as Y2-authentic merely because it parses.

## Resources, stop conditions, and review

Primary-only cap 420 seconds, no carryover; one focused `yu-playground` Cargo
test process at a time. Stop on any hash mismatch, non-comment `--` occurrence,
projection that alters code bytes, syntax diagnostic, structural recovery,
source-byte mismatch or direct-root discrepancy. Preserve exact falsifiers.
No independent reviewer or writer is assigned; result remains provisional.

R149 imported ModuleMap identity, actual `ComputedDef`/`Expr` publication,
root specialization, Request reachability, Types output, Console host writes,
Simple-sub/evaluator A/B, R70/R71, source/native proofs, soundness,
principality and production all remain OPEN. Next material boundary: identify
an authentic Y2 registration interface if this projection cannot establish
source-root correspondence.
