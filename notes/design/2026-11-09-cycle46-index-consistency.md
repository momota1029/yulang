# Cycle46: constructive consistency for the checked string Index adapter

Status: Draft, 2026-11-09. Scope: the existing finite named-source string Index fragment.

Data: finite source occurrence table, named request list, and an actual initial State restricted to a syntactically specified all-string-compatible fragment. Source extraction remains input, not a parser theorem.

Independent contract: all-string assignment satisfies the permitted initial atoms and source identity. Every propagated slot constraint is string equality. Construct the output model, rather than assuming one.

Execution: reuse checked scope validation and the actual producer trace. For every table and request list with valid scope and every initial State in the stated fragment, construct a successful output and an Executed trace without a final-model premise. Regression must include shared occurrences and a nonempty two-step Index chain.

Limits: no claim for arbitrary initial states, general declarations, source parsing, or general B4. No language rejection semantics are chosen. Scope errors keep the existing adapter diagnostics.
