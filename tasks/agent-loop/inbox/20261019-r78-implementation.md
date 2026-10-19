# R78 implementation/design handoff

Sprint contract SHA-256: `bf68454c19a7b4cfe5168355e0e5fb73beec069ad57dd53678258a66f26dfcab`  
Author/owner: Luna primary  
Claim class: decision-ready design proposal; no adopted semantics or implementation

Read-only owner evidence locators and hashes are frozen in `tasks/agent-loop/current.json`. Existing source projection distinguishes exact FieldTail receiver prefix/member and exact RoleDeclaration/ImplDeclaration nodes. The ordinary local source form and provisional playground currently do not resolve or execute methods.

Draft result: `notes/design/2026-10-19-r78-executable-method-role-pilot.md`. Surface/status map: `notes/progress/2026-10-19-r78-surface-readiness.md`. The proposed pilot reuses `receiver.method(args)` syntax, exact role and impl occurrences, unique type/role/member lookup, field-first fallback, explicit evaluation order, and ordinary Apply lowering. These are candidate choices only.

Missing decisions: declaration meaning, whether impl description names a role, field/method collision behavior, lookup visibility/ambiguity, receiver/argument evaluation order, role signature checking, and adoption path. The 2026-10-17 ordinary Call formation proposal is unadopted gap evidence; the playground is provisional. Independent reviews and explicit user approval are required before source/test/runtime edits.

R76/R77 source correspondence can be reused only within its pinned scope. R77 rev1 failure remains frozen; rev2 remains inactive. No source files, tests, expected outputs, or runtime behavior were changed. No commands/tests/probes/builds ran for this design lane.

Next: fresh independent compiler/source and spec/design review of both R78 artifacts; then present the exact decision set to the user. Writer stopped for this artifact revision; further R78 design work remains Luna-owned under the active contract.
