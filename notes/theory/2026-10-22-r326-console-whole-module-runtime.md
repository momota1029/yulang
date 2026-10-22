# R326 — unchanged Console and whole-module execution

## Parent

The unchanged-samples goal remains broader than the Types and Console pair. R149 fixes the exact 92-byte Console source and its two captured write events, in source order:

```yu
// println is a library effect handled by the host.

println "hello from Yulang"
say: 1 + 2
```

Expected CLI output is `hello from Yulang\n3\n`. R325 now runs the exact Types sample and captures `(42, Yulang)\n` through an exact source-operation import identity and the saved continuation template.

## R326 claim

The runtime must run the original mixed source schedule without requiring an arbitrarily selected definition. It must visit every expression/computation root in source order, retain lazy value materialization and initialization behavior, and complete only after the schedule has drained. The Console source has no injected `main` definition, so selected-definition execution alone cannot meet this behavior.

Host operation handling reuses R325's exact `SourceOperationPathImport` capability, the resolved export identity, and the checked `str -> ()` signature. Runtime dispatch compares `SourceOperationId`, validates each actual string payload, captures one event, supplies unit, and resumes the corresponding saved continuation once. The CLI concatenates the two payloads in source order. A source/native proof, full `out::write` adequacy proof, solver soundness, principality, and other Yulang2 samples remain open.

## Evidence and next premises

The exact source hash is `ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`. Completion requires ordinary candidate inference and actual CLI execution with the original bytes, plus preservation tests for selected-definition mode. These executable checks establish only the bounded implementation path. General schedule coverage, source correspondence, and the parent proof need separate evidence and review.

Contravariant `[io]` annotations continue to mean `[io,'e]`; `[state]` is permitted. No implementation may tighten that rule to make the samples pass.
