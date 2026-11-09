# Cycle23: speculative support has no fixedpoint

Draft implementation question; no new language decision taken.

Cycle22's first-hit parent now receives a real associated-type equation rather than
an arbitrary ordinary update. The checked `Index(box int, int).value = int` declaration
is used by the child-to-token annotation. Empty token set enables the child; the token
sets the shared slot to int, so the earlier literal displaces that child. Neither of
the two subsets is self-supported. This is proved in CommonRoleSupportSearchBoundary.
It refutes universal associated-only emission monotonicity for the supplied map.

Yulang-shaped illustration (not parser/run checked):
```yulang
role Parent 'a
role Child 'a
impl Parent (box int)
impl Parent (box 'a) where Child 'a
-- The child asks Index(box int, int).value and equates it with 'a.
```
The source annotation lowering of the last comment is not proved. This is not a claim
that the language is inconsistent. Both frontiers are unselected (pending/ambiguous).

1. Delay final commitment and retain candidate guards until sibling stabilization
   (preferred; consistent with existing spec6.3). Need a guarded-equation carrier.
2. Treat speculative feedback fixedpoints as accepted solutions: not recommended;
   even existence fails here, and self-support need not be grounded.

No choice is needed to use the new exhaustive search as diagnostics. It does not
replace the language resolver or interpret empty search as a language error.
