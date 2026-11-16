# Reachable nonrepeating-head conservativity (cycle220)

Status: Draft proof plan, I-41 semantics unchanged.

Objective: isolate the general fragment where the new sharing diagnostic cannot
change V7 selection. No old definitions or source judgments are modified.

For a reachable state of DefaultBoundary208 and a current candidate Frame,
Precision220 derives observation existence and functionality from the actual
initial-source trace. If equal-named head uses have equal origins
(`NoDistinctSameName`), every current journal model satisfies the explicit
sharing equations. A nodup list of head-use names is a sufficient syntactic
condition, not a restriction added to the language.

Planned quantified statements:
1. For every reachable state, eligible frame and current journal model,
   NoDistinctSameName implies Holds of that frame in that model. Reachability
   supplies InitialSource, point roots, GroundRoots, Coverage and the Step trace;
   there is no free constructor-injectivity or observation premise.
2. Adding existence of a current journal model yields Feasible for that key.
3. If the same key is the unique V7 survivor, sharing Conflict is impossible.
   This third result does not require model inhabitation: a supposed Conflict
   itself supplies a model, and item 1 contradicts its infeasibility clause.
4. Consequently a V7-selected node with such a frame is V8-selected, including
   states with no models. The exact converse already follows from V8 selection.

Scope: this is a named nonrepeating-head fragment, not unconditional EvidenceNode
or full B4 completion. It concerns current frame sharing, not simultaneous
journal/packet/effect witnesses. All proofs will be focused-built and audited.
