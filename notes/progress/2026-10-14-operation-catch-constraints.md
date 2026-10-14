# Operation Catch payload and raw-continuation construction

Date: 2026-10-14
Branch: `research/simple-sub-intrusion`
Baseline: `5467189445fd04a4c5f2090f6fe3e96609162a47`
Status: monomorphic private-carrier slice verified and reviewed; residual/hygiene OPEN
Mode: M2, compiler_referee and spec_auditor; zero performance measurements

## Authority and implementation

The user requested continued effects/handler implementation with the playground
and proofs. This slice uses the approved operation-pattern contract, top-level
inference principles and charter §§9,13–20. It introduces no new source meaning
or negative-formal permission map. The candidate remains a research path.

HIR retains resolved operation declarations, payload patterns and a raw
continuation pattern. Payload and continuation binders have separate arm-owned
identities and lexical scopes. Expression and pattern operation names share
the same namespace/visibility resolver. Empty call-pattern syntax follows
Oracle's wildcard payload behavior; it does not require a Unit payload.
Normal value arms retain their previous identities and scope restoration.

Before each arm body, the solver forms paired declaration-value ports: payload
A from `op : A -> B`, continuation response B and original scrutinee result V.
One signature environment is shared. Referenced binder representatives retain
their arm introduction level even when first used in a deeper initializer.
Without a value arm, the original normal-return value reaches the result.

Raw continuation construction uses the existing Value-entry rule. Fresh effect
rows E/R retain `E <= R` and original scrutinee `S <= R`; both Function
polarities share these rows and original V. Response computations execute
outside the selected handler, and their effects reach R. No handler is
reinstalled. Whole S is a provisional conservative suffix envelope: a no-suffix
raw continuation can be pure. All scrutinee and arm-body effects still reach
the Catch output. No residual subtraction is installed.

Preflight follows the actual referenced packet fields and value/latent-port
construction. Wildcards and unused binders do not demand unavailable callback
interfaces. A primitive response's root operation-computation row is retained
by ordinary invocation, not mistaken for a negative callback port. Used
unsupported nested negative concrete interfaces return `Unsupported`, not
resource exhaustion. Generic arms still require charter §§19–20's rigid
existential owner. Guards, labels, non-total/tuple patterns and more general
operation heads also remain incomplete carrier paths, not language rejections.

The [playground example](../../tools/inference-playground/examples/catch-operation.yu)
has an `int` payload and `str` response, checks the payload and invokes the
raw continuation. CLI tests distinguish payload/response conflicts from
unsupported-source failures. No Catch-result reference fragment, request token,
watcher or alternative inference engine is added.

## Proof consumption and next implementation owner

The independently reviewed [boundary derivation](../theory/2026-10-14-handler-boundary-construction.md)
supplies a conditional finite suffix-envelope argument under explicit sound
Call/signature and joint lifecycle premises. It does not close those premises
or prove exact suffix equality. The valid no-suffix ping construction refutes
that equality without refuting conservative abstraction. Separate code review
checks E/R; the baseline theorem does not silently include concurrent changes.

Eligibility U remains OPEN. Omitted/wildcard callback contracts still protect
corresponding typed paths; disabling negative concrete formals does not remove
that protection. Zero-word storage cannot establish source eligibility. Next
is the actual callback-profile constructor and live Function-port/context
consumer in the note's §6, using the existing hygiene theorem at its original
hypotheses. The reviewed native residual primitive P is available once this
construction supplies eligible input and preserves protected same-family
paths. Another conditional proof assuming the absent constructor is not the
next action. Complete Call, hygiene, soundness, required principality and
production cutover remain OPEN.

The actual prover launch succeeded as `prover`, requested Sol/high; effective
runtime model/effort metadata was unavailable. It used one research-note lease,
no children and no executable experiments. A separate compiler_referee
accepted only the bounded conclusions above.

## Review and cost

Independent compiler_referee and spec_auditor reviews covered source/solver
semantics and exact conformance. Focused execution and review found an initial
collection-term/live-port mismatch, missing response entry-effect forwarding,
an overwritten binder introduction level and preflight mismatches with paired
ports actually constructed. Batched repairs fixed those owners, including
used/unused and root-computation-row controls. Delta reviews closed all major
findings. Fact/work counters include both k ports and its two effect relations.
Existing semantic expectations were preserved.

Construction and binder-use indexing are linear in source expressions, arms
and payloads; paired signature traversal is linear in relevant signature size
per arm. Each used continuation adds two effect rows and two native effect
relations. Existing propagation, lifecycle and resource accounting are reused.
No timing decision required a performance reviewer or benchmark.

## Verification

Primary Cargo processes were serialized with `CARGO_BUILD_JOBS=2 timeout 300s`;
test processes used `--test-threads=1`. Final code results:

| Command after `cargo` | Result |
| --- | --- |
| `test -q -p yu-hir --features shadow --test catch_local_source --test conditional_local_source -- --test-threads=1` | 6 + 6 passed |
| `test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --test candidate_operation_catch --test candidate_catch_value_source --test candidate_operation_source --test candidate_value_entry_effect --test candidate_formal_effect_polarity --test candidate_conditionals -- --test-threads=1` | 12 + 6 + 5 + 2 + 6 + 10 passed |
| `test -q -p yu-playground --test cli -- --test-threads=1` | 19 passed |
| `check -q --workspace` | Passed, warning-free |

These are 72 distinct passing tests. Initial raw-k failures are resolved;
earlier passes are not counted again. No full workspace test suite, ignored
test, benchmark or performance sample was run. Whitespace, explicit diff scope
and local record links were checked. No broad check was repeated for record
updates. Deterministic checks do not replace review or metatheory.

Primary synchronization covers this checkpoint, `tasks/current.md`,
`tasks/research-lab.md`, the design index and boundary note's review receipt.
No shared record is deferred. All producer leases are frozen; integration and
the coherent upstream push belong to the primary.
