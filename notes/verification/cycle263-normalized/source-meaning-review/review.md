# Independent review: source-derived meaning certificate

Reviewed exact coordinator commit `640ae837f0a83a60fc8a1045a2783ed7cc2c1080`, including new dependencies UniversalMeaning263 and UniversalTrace263. No reviewed production code was edited.

## Verdict

No correctness or quantifier-order defect found. The theorem is a conditional semantic certificate over an explicitly strengthened context, not automatic source correctness. Its interpretation is genuinely fixed before base, inspector, execution endpoints, and assignments are quantified.

## Quantifiers and interpretation

`source_certificate` has `∃ owners, ∃ pool, ∃ holds, ∀ base inspect ...`. Source bounds are chosen once; the nonempty representative family is selected solely from actual source-reachable registered plans. Neither arbitrary `base` nor the externally supplied inspector can influence `holds`. Representatives are mathematical classical choice, not executable discovery of future Plans. `Certificate` chooses one event list before `∀ assignment`; event sources and chosen root/Plan/owner are exact snapshots from the successful finite run, so meaning is simultaneous across assignments.

## Strong context, explicitly scoped

The model parameter is **Context base registry root start**, definitionally `base assignment ∧ SourceHeads registry root start assignment`. SourceHeads quantifies over every reachable snapshot and every registered plan's actual head schema. It is stronger than the user's base and is NOT shown to follow from source Initial, one snapshot's Models, current Ready, or successful finite execution. It can exclude assignments and could be empty for some source programs. No model-existence/SAT claim is made.

The context contains no body/output ClassEffects premises. The proof routes only its head component into representative_compatible, and the earlier source-center induction derives normalized binder/center support. Thus this is not the circular shortcut of assuming all output effects to prove the finite-write effect equation. It still leaves an explicit future obligation: establish a useful inhabited SourceHeads context or weaken the producer if a stronger compiler statement is desired.

The operational Plan-free finite algorithm does not need SourceHeads. That assumption enters only its conditional meaning interpretation. UniversalMeaning.actual_proposal interprets actual emitted keys and uses owner separation plus normalized semantic transport; reserved unused keys need not have been compiled by a representative. The write equation retains prior finite Models and adds actual selected ClassEffects.

## Empty case

The empty branch assumes no registered Plan occurs anywhere on any source path, not merely that the initial journal is empty. `empty_selected` correctly derives that every inspector output has an empty selection list. Observation is therefore constantly empty, validation constantly succeeds, and any successful run returns its input state. The proof supplies an empty event history, final Ready, terminality and the identity model equation with `holds := True`. It does not invent a Plan inhabitant or representative family. Existing finite-state content remains unchanged; it does not claim that the universal basis itself must be empty.

## Limits retained

The inspector is externally supplied and must return source-reachable snapshots for all finite states. Consecutive observations are not proven consecutive old-source Steps. The count bounds effective finite writes, not source execution or observer cost. Successful validation is not source-language acceptance or satisfiability. The certificate preserves the explicit head context on both sides of its model equivalence; it does not erase that context in the conclusion.

## Independent verification

A separate temporary source tree exports exact reviewed sources. A separate review cache freshly compiles UniversalMeaning263, UniversalTrace263 and SourceMeaning263 with `--trust=0 -DwarningAsError=true`. Prior independently audited dependencies are reused. Source hashes and logs are adjacent. The standalone audit imports only Yulang production modules and prints axioms for nine principal theorems. All are within standard propext/Classical.choice/Quot.sound; no new axioms, sorry or native_decide were introduced.
