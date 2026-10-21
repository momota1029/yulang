# R257 result — Y2 playground source-input bridge

Status: primary-only read-only locator result; no independent review.

The exact Types/Console Web examples flow from `main.ts`'s example source into
the textarea, then through `runSource` and `run-worker.ts` to the WASM
`run(source, lang)` entry. The full embedded-std branch forwards the same
source argument to Yulang's source-build or artifact-backed source-build
entry. Y2's source owner constructs the root `SourceFile` at the default
module path with its implicit prelude/module prefix; `sources::load` creates
the CST through the pinned parser entrypoint.

This pins the parser/input owners and narrows the remaining identity join. It
does not identify the actual sample's registered declaration DefIds, root
order, specialization, or Request reachability. Those remain UNKNOWN. No
sample execution, tests, builds, code changes, or production gate changes.

Details, exact blob pins, and limits: `tasks/agent-loop/sprints/yulang2-playground-input-identity-20261021-r257.md`.
