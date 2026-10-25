# Declaration substitution — r5 handoff

Outcome: primary-authored Lean candidate; checked, not independently reviewed.

`notes/theory/lean/YulangClosure/DeclSubst.lean` contains the repaired
declaration-instantiation substitution theorem and two applications:

- `operation_declaration_instantiation_subst`
- `operation_instance_instantiates_subst`
- `operation_instance_instantiatesIn_subst`

The target theorem uses explicit field extensionality and substitution
composition; the failed `OperationInstance.mk.injEq.mpr` term is absent. The
module compiled after building `YulangClosure.PaperTypeFormation`; scratch
source and dependency hashes and the exact check are recorded in the r5
contract. No project-specific axiom was introduced by the source, but a
separate axiom audit and fresh independent review remain pending.

Parent application: this supplies a declaration/argument-substitution lemma
for the original typing-substitution path. It does not establish the full
typing-substitution theorem or any inference, executor, source/native, or A/B
closure. Next work should take the theorem to the exact paper obligation and
prove or expose its next missing premise.

The prior r3/r4 failed snapshots remain preserved. Eight UNKNOWN reservations
remain quarantined; no worker cessation was inferred from their absence in the
current collaboration tree. No reviewer ran and no production authority was
created.
