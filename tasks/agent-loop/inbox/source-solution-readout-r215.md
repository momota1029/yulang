# R215 primary handoff — shared source/solution readout

Assignment: R215 / Luna primary, abstract model construction, 1,800 seconds. Baseline `yulang3/4f75aeeec`. Parent: unchanged `Contracts.SourceProblem.InferenceSoundness`, full original quantifiers and one shared assignment witness.

Required: concrete independent assignment/regular-graph meaning and source readout; exact source-independent equations for all L1 literals and the same original annotation ID/formal scope/entry; application sites in the parent proof shape; permission/inflow/residual remain distinct. Annotation synthesis and written target remain distinct. No `Kernel`, source judgment, `LiteralAtom`, or new atom may be assumed to supply the bridge.

Falsifiers: incompatible readout for equivalent satisfying graphs; literal descriptor/value/root/event mismatch; source subsumption unavailable; annotation owner/path/scope or symbolic connection lost; permission creates inflow, deletes unmatched `write`, or merges siblings. Stop at the first exact missing equation if no construction follows from fixed authorities.

Dependencies and hashes: see sprint contract `tasks/agent-loop/sprints/source-solution-readout-r215.md`. Output: `notes/theory/2026-11-02-source-solution-readout-r215.md`. R208 `StaticAnnotationConstraintInterpretation.lean` is unverified, does not connect the original Kernel atom, and is not adopted.

Implementation: `NO_SAFE_CODE_SLICE`; no Rust edit. Pinned Lean 4.35.0/cache use is allowed only for equation verification; primary owns `.lake/build` output. No new environment or dependency update. Fresh review after freeze, 600 seconds. Parent accounting starts and remains **0/4 roots; 0/5 packages** unless a reviewed original premise is applied.

Worker state: Luna is the only active author. No theorem lane admitted. No Rust, tests, Cargo, or native correspondence work. Writes stop at 1,800 seconds or earlier exact authority blocker.
