# R315 — reviewed partial outcome

Baseline `a87db9a8e`; contract `tasks/agent-loop/sprints/module-context-binding-r315.md`
SHA-256 `00e98ec431011a89bd42ffd0ea872bc0a631880f34206004786917b9a55953fd`.

The same-run test-only source witness now retains the private `make` declaration,
ordered module bindings, full selected initializer, original name use, global
definition cell and provider. The Lean artifact computes the example's
published binding and applies its lookup to the existing R314/R313 consumer.
Its R159/R311 application preserves the original kernel and all semantic
premises. Internal `.published` is not public export visibility.

Independent source review found a foreign-snapshot acceptance and a hardcoded
cell interface. Both were repaired, with clone, second-Machine and mutated-cell
negative checks; independent delta review accepted the fixes. Producer focused
Cargo test: 1 passed. DefId/realm/scope mutation coverage is not complete.

Independent Lean review passed the finite structural and conditional claims.
Pinned Lean 4.35.0 target and all 31 theorem type/kind/complete-axiom audits
passed at `-j1 -M2048`; only `propext`, `Classical.choice`, and `Quot.sound`
occur. The normal `-M1024` checker exhausted memory; this is a retained
limitation, not a pass. Independent audit log SHA-256
`656bcc071cea8c1c7c2227d82022cd90ef30ff0b8f4b119ba2941756c143e144`.

Frozen Lean SHA-256 `7adcf88c1ff98c5c4cf23aa788bf5713ddcb949dd09775fb0bd542fe1e2ac577`;
native generated evidence `/tmp/yulang-r315-native/module-context-binding-r3.lean`
SHA-256 `de228fdc6b984373048107ff1bc69a25620dea6a36cb3340f143b6b161f6fc95`.
Producer handoffs: `tasks/agent-loop/inbox/module-context-binding-r315.md` and
`tasks/agent-loop/inbox/module-context-binding-r315-source.md`.

Parent audit: lexical provenance is reduced for this example. No original R159
semantic premise is discharged. Original publication environment/readback and
coordinates, `raw.program` correspondence, admission, descriptor formation,
Checking, semantic Return, independent arms/licenses/futures and q_c remain
open. A rejected App admission still falsifies any implication from lookup
alone to the parent judgment. No whole-language or production closure claimed.
