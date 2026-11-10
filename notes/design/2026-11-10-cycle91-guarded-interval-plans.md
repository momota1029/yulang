# Cycle91: guarded recursive interval plans

Status: Draft implementation boundary, 2026-11-10.

Objective: compile the fixed Form interval grammar into finite alternative plans, recursively requiring every where child, and prove exact ordinary models with one shared source valuation. This closes the guarded-plan subgoal of bridge 2, not state-dependent saturation or B4.

Data: a plan is a finite ordered demand list. A declaration branch emits its actual captured demands. All children of that branch are conjoined by Cartesian product of their plans; different candidate declarations remain alternative plans. An empty requirement list has one empty continuation; a child with no accepted branch has no complete plan. Unsupported local inspections remain separately visible through cycle90 boundaries and are never reported as language rejection.

Independent judgment: at fixed ambient assignment and fixed shared values, a goal has a finite derivation when a registry declaration has an independent Accepts capture, its original head fits those values, and every original requirement has a recursively derived child. It does not mention the plan compiler. Invocation source names are supplied by Goal → Declaration → binder → source; this is a restricted boundary input: equal goal/declaration/binder tuples necessarily reuse a key, so repeated invocations cannot be independently named. This is not an occurrence-sensitive source allocator or an approved general source policy.

Execution: compile accepted branches recursively using the existing checked declaration's strict decrease in both endpoints. No fuel, visited list, candidate success, or model is an input. Only the fixed endpoint syntax and checked finite registry control recursion.

Main theorem: for every registry passing its real checker, arbitrary root, endpoint slots, source-key map, old demands and ambient assignment, an emitted plan has a model under the real ordinary generate iff there exists one global source valuation satisfying the old demands and the independent recursive judgment. Shared values are outside all sibling and candidate choices. Different plans are not conjoined. Source identities/slots remain supplied, and child demand consistency is not a dictionary or four-way classification.

Design reason: general Form materialization cannot simply be identified with the int-only/unary State adapter. No such translation is available. The alternate cycle90 goal avoids claiming arbitrary future-state finiteness. No new language semantics are selected. spec 6.3 supplies conjunction of siblings and declaration Paterson decrease. Prior Yulang2 x-oracle C3-PARENT/C3-PARENT-NEG supports positive/missing-child examples only; no new runtime comparison is claimed.
