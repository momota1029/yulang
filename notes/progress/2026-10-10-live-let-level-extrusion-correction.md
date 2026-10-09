# Live let scheme correction

Date: 2026-10-10
Authority: current explicit user correction
Mode: M0 record; bounded read-only architect audit

The primary claimed completed initializer solving/generalization must precede
continuation solving. The user rejected that claim with levels and extrusion.
The mandatory solve/freeze/install barrier is withdrawn.

The pinned [reference](https://raw.githubusercontent.com/LPTK/simple-sub/9bae772624c23b52a93c1b226157e16898b4d9db/shared/src/main/scala/simplesub/Typer.scala)
returns a scheme containing a boundary and live type graph. Consider
`(\g -> let f = \x -> g x in f) succ`. The local application extrudes younger
argument/result coordinates into older approximants shared through `g`.
After the local scheme is used, outer application supplies integer constraints
through those older coordinates. The scheme was not a completed snapshot.
This is a symbolic trace, not executed evidence.

The corrected adapter retains each local's actual live root and boundary.
At each use it captures the current graph as temporary freshening input,
copies eligible coordinates and shares older anchors. Source traversal can
use existing immediate constraint operations without claiming final saturation.
Deferred intrinsic RHS relations would need transport under the same use map;
copying an unconstrained young coordinate and omitting its later bound is also
unjustified. No such deferred engine is required for this private adapter.

The implementer stopped the incomplete patch and resumed only after this
correction. Useful level/source ownership and one-shot initializer effects are
preserved. No tests, builds, probes or measurements ran for this audit.
Full Call and target-branch replacement remain open.
