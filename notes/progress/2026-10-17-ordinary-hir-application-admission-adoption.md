# Adoption receipt: ordinary HIR application admission, direction A

The user explicitly adopted revision 4 of
`notes/design/2026-10-17-ordinary-hir-application-admission-successor.md`
(SHA-256 `2e61e2acb1a8981bb78592accc48207a24a5cc4c75278e100f63eb960acfeea3`)
and its exact §7 supersessions. This includes the stated observable consequence
that `HirErrorId` and `HirDiagnosticId` remain dense final-vector indices within
each module while downstream numeric values may shift after deletion of an
admission error or insertion of operand diagnostics. No sparse IDs or tombstones
are adopted.

Direction A is now an approved structural HIR policy for the binding-body
grammar `Atom | Group(E) | Apply_ml(E,E) | Apply_call(E,E)`, under all recovery,
association, source-key, allocation, error, carrier, and atomic-publication
conditions in rev4. Root identity follows the outer retained constructor. A
retained Group keeps its own ParenthesizedExpression key. Existing ordinary
source-carrier outcomes and occurrence ordinals are preserved; canonical HIR
children are appended afterward and mapped to exact parse-branded keys.

This admission does not assign Call typing, type/effect solving, source `T`,
source/native adequacy, or production meaning. Original A/B quantifiers,
F1/FK1, N-Transport, Call adequacy, soundness, principality, termination and
production gates remain unchanged and OPEN. No theorem conclusion is weakened.

The user also authorized proactive candidate interpretations and inference
rules for advancing proofs. Within the fixed rev4 grammar and original theorem
quantifiers, the sprint may formulate derived judgments, prove their premises
and preservation, and use counterexamples to refine them. A candidate rule must
not assume its conclusion, silently enlarge admission, or identify structural
HIR application with semantic Call. Any proposed rule changing observable
source behavior, response/challenge admission, or an original theorem domain
must state its exact meaning and compatibility consequences before dependent
production use.
