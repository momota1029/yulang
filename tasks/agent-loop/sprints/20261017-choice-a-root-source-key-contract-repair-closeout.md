# Closeout: choice-a-root-source-key-contract-repair-20261017

Status: CLOSED-REVIEWED-PARTIAL at baseline `a640dd909132b2be1d1bbbe35a4249e16642b84b`.

Fresh spec review of successor revision 3 was CLEAN. It confirmed that the
previous body-root mapping gap is repaired, collision handling is explicit,
and atomic post-carrier mapping is plausible. The compiler review confirmed
those points and the fixed-literal source audit, but found a MAJOR constructor
seam: the grammar retains `Group(E)` as a possible complete body while the
preserved body-root occurrence rule covers only Apply and Atom. In
`my z = (f x)`, Group and inner Apply need distinct IDs and distinct exact keys.

No Group elision was authorized. Remaining compiler/architect review capacity
was stopped; no code/tests were authorized or run. Original theorem gates remain
OPEN. Successor rev3 and handoff rev3 remain frozen in Git commit `a640dd909`.

The focused Atom/Apply/Group ownership repair and bounded review sequence are
recorded in `tasks/agent-loop/sprints/choice-a-group-root-ownership-repair-20261017.md`.
The predecessor's remaining 220s are retired.
