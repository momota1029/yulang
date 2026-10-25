# R37 Luna source/control intake — let-push and current-port boundary

Sprint `PAPER-CURRENT-PORT-LET-PUSH-20261026/r37`, contract SHA-256
`98e9367deca5f6f4d1bd4541b4caba87a431df8c7c8e24f2b0e7cb9e7c93b3d1`.
Baseline `858eb47b0`; sprint admission `7c94d46d5`.
Outcome class: source/control evidence and precise missing-premise report. No Lean
proof, source/native closure, or original-parent closure is claimed.

## Let-push evidence

The manuscript ordinary reduction at `docs/yulang-operational-type-safety-ja.tex:305`
contracts `let x ← Ret v in N` to `N[v/x]`. At `:331–334`, a let's unique
active child takes one step in place; `Fail`/`Bad` propagate, while normal return
and request use special rules. The frame typing lemma at `:1014–1026` gives an
intermediate type for the active hole and reconstructs the enclosing let frame.

R36's exact auxiliary transition is in
`notes/theory/lean/YulangClosure/PaperCoreControl.lean:11–45`: for a state
`⟨.letE first body, stack⟩`, `controlStep` returns
`⟨first, body :: stack⟩`. The first list element is the innermost pending body.
`plug (body :: stack) first = plug stack (.letE first body)`, so `erase` is
identical across this focus/push transition. `StateTyped` and `StackTyped` retain
the same `DeclarationTable`, `GraphEnvironment`, `TypeEnvironment`, and final
result type while the active head may have a distinct intermediate type.
The r2 theorem proves this syntax-level stutter and finite-let typing fact.

This R36 push is a proof-state focus/decomposition transition. It is not by itself
a manuscript machine reduction: the manuscript steps the child in place. The
relationship between that proof focus and the full machine configuration must
therefore be supplied by an embedding or simulation relation.

## Full-state and port evidence

The manuscript full-state judgment at `docs/yulang-operational-type-safety-ja.tex:1845–1858`
requires current finite evidence for (1) the value graph and active-code execution
typing, (2) each code label's precise local derivation and the same typed instance
for free values, (3) active/saved frame derivations, and (4) membership of the
currently used interface diagram in its input `V` set plus pending events/queries
in their current ports. A stale heap activity snapshot is explicitly not required;
re-observation supplies current interface facts when a value is next used.

The parent at `:1861–1864` requires the successor to use the same typed derivation
graph's residual or an explicitly declared latent/reentry instance, retain value
type, and establish each current-port concrete diagram's inclusion in its
abstract set. Fresh immutable graph extension and uniform binder renaming are
allowed. The Horn definition at `:1544–1559` requires `F_G(U) ⊆ U`, input
inclusion for every consistent joint assignment `η`, and forbids choosing `η`
independently per port or arbitrarily narrowing formal-input seeds. The bind row
at `:1529` connects the first computation's result to the body's bound input and
checks the body for every type-compatible input diagram.

## Exact gap and owner

The inspected Lean syntax (`PaperExecutionSyntax.lean`) has `Computation.letE`
but no full runtime state, source-code label, port table `U`, assignment `η`,
or concrete diagram. R36 `PaperCoreControl.State` contains only a computation
head and a list of let bodies; its typing contexts are not the manuscript's typed
derivation graph `G`, current environment/assignment `η`, or interface table `U`.
The inspected files define no relation from a manuscript full state `C` to an
R36 state, and no let-specific theorem identifying the child's code label and
input port after focus decomposition.

Therefore the five requested facts resolve as follows:

1. **Before/after full-state evidence:** the manuscript requires the four current
evidence components above; no explicit full-state tuple transition for R36 push
is defined. Since push is only a focus change, an embedding should keep the same
machine configuration and move the active-hole decomposition into R36's stack.
2. **Head/stack map:** the syntax map is exact: head `first`, stack `body :: stack`,
with the first stored frame innermost. No formal full-state projection establishes
that map yet.
3. **Derivation graph, `η`, and `U`:** manuscript-level let composition requires
one shared assignment and the post-fixed Horn table. R36 carries none of those
objects; no proof transports their identity or membership across the focus map.
4. **Next code label/input port and concrete membership:** R36 has no code-label
or port fields. The manuscript requires current-interface input membership and
binds the body's input to the first computation's result, but the inspected
sources do not identify which concrete current input port belongs to the newly
focused child or derive its diagram membership from the parent state's evidence.
5. **First missing premise/owner:** Luna's source/control lane must define and
prove a full-state-to-R36-focus relation for let frames. Its let-push clause must
preserve the identical `G`, joint `η`, and `U`, identify the active child's label
and input port, and derive that port's concrete membership from the current
full-state evidence plus the bind/active-frame derivation. Until this is supplied,
there is no Lean proposition whose current-port preservation follows from R36
`erasure`; erasure equality alone is not a port-membership proof.

Falsifiers: any proposed map that concludes port preservation only from equal
erasures; assigns a different `η` to each port; narrows a formal seed; treats an
old heap activity snapshot as current; changes `G`/`U` during auxiliary focus
push without an explicit graph-extension rule; or cannot identify the child's
actual input port and its concrete-membership premise.

## Boundary and disposition

This packet found a specific missing bridge definition, not a counterexample to
the manuscript theorem. The original one-step parent, full machine-state/control
correspondence, all other frames, full source/native, inference A/B, and production
remain OPEN. No semantic interpretation was selected and no implementation slice
is safe: `NO_SAFE_CODE_SLICE` after inspecting the R36 proof owner
`PaperCoreControl.lean` and actual syntax owner `PaperExecutionSyntax.lean`.

Inputs rechecked against the frozen R37 contract: manuscript
`a003b56a2f32eed06a2c604ef8aed043d43752cbed0b09028eff7f6efac4886b`,
R36 source `261d6a77438eec1a32e0299b73583899204ed7c2fe0590b819ecd3fd5b89876e`,
R36 contract `84c679419e1fd4cb75f4d16e2c2b9c537f0f10e5b29ac6d5fe885e697079bfe2`,
R36 handoff `bc4046485dccea2750f1e24b91696ba0ba2c0fe52fc05bbf5bce3e8e0fcffeac`,
`PaperExecutionSyntax.lean` `e38cd059caf7d81549a09f360d81e52cb4aecb8a95d8eb3f308ffda7d38a8932`,
and R35 `PaperCoreStep.lean`
`503f81c162f7b9ceb0f7d27aa9796b8d7010345653267c675267ce14214c57e9`.
No checker/native calls, workers, descendants, tests, Git dependency changes, or
implementation writes. R37 spent under its Luna-only 600s grant; exact active
seconds are not independently metered. R36's remaining budget was not reused.
