# R236 outcome — canonical literal generator candidate

## Original obligation

Unchanged parent: `YulangClosure.SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`. This sprint tested
whether a direct canonical literal construction can connect original literal
payloads to the original symbolic `Build` node under the adopted L1 table.

## Result

The candidate maps all eight `OriginalSource.Literal` payload forms to the
matching `PaperTypes.Literal`, constructs the adopted canonical type and value,
retains supplied site/root/event/scope/witness coordinates, and consumes
R196's actual payload-bearing symbolic `Build` atom. The seven named Lean
declarations and complete printed types/axioms are recorded in
`tasks/agent-loop/inbox/canonical-literal-generator-r236.md`; pinned Lean
4.35.0/Lake 5.0.0 checker passed. Axioms are `[]` for the two L1 type/value
equations, `[propext]` for coordinate preservation and direct atom generation,
and `[propext, Classical.choice, Quot.sound]` for equations involving R196's
Build formula.

Independent review passed the candidate's bounded source mapping and exact
consumer, but found an algorithm-authority blocker: adopted L1 fixes type/value
meanings without supplying a generator clause, while the pinned Simple-sub
branch directly generates only integer literals. The all-eight direct
extension therefore remains a candidate until its owning generation
correspondence is established or any required algorithm decision is approved.

## Parent and root accounting

Parent-premise delta: **0**. Closed roots: **0/4**. This construction does not
interpret every satisfying assignment, build intrinsic effect/pure Return,
authenticate source coordinates, discharge contextual admission or construct
the shared `sameScoped` witness. No soundness, principality or termination root
closes here. No source semantics or supported forms changed.

## Resources and repository boundary

The existing `notes/theory/lean/.lake` grew from 134,587,836 to 144,880,556
bytes (**10,292,720 bytes**) during pinned checking, below the 64 MiB sprint
bound. This used the existing cache only; no environment, worktree, target or
new cache path was created. No Rust/Cargo or general tests ran. Unrelated dirty
files and UNKNOWN/quarantined paths were preserved.

## Next root-first action

At the next sprint boundary, dispatch against this exact missing owner
correspondence and the unchanged parent. Do not count the candidate as an
authorized generation theorem or repeat quotient-only work. The pending typed
Union decision remains independent of this literal finding.
