# Cycle24: candidate guards are metadata, not a selection policy

Cycle23 found self-disabling first-hit support. Cycle24 retains later candidate
children and their guarded equations, even when an earlier candidate matches.
No source acceptance rule is introduced. spec6.3 delayed finalization is unchanged.

Yulang-shaped illustration (not parser/run checked):
```yulang
role Parent 'a
role Child 'a
impl Parent (box int)
impl Parent (box 'a) where Child 'a
```
An associated-type equality from a child may narrow the shared slot to int.
A first-hit producer can then switch to the earlier literal candidate.
The new metadata carrier retains the later candidate, but does not choose it.

1. Delay commitment, retaining candidate-specific guards until sibling stabilization
   (preferred, consistent with spec6.3); establish how correlated ancestor alternatives
   are represented before deriving a final diagnostic tree.
2. Conjoin all candidates' equations unconditionally: not adopted; incompatible
   alternatives could be conflated.

The current mask is per source-node/candidate, not per complete path. Different
ancestor alternatives that merge at a source node lose their path correlation.
No new language design decision is made; guarded-collection exactness is independent
of selecting a policy. Next work must not treat an arbitrary mask as a valid choice.
