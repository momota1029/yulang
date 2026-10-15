# Receipt: initialization effect-order observation

Date: 2026-10-16
Question: `2026-10-16-initialization-effect-order-observation`, revision 1
Approved draft: `initialization-effect-order-observation-a1`, revision 1
Integrated bundle: `6b6cafea1`
Outcome: validated and consumed; option 1 selects actual outward initializer effects

## Validation

Validated SHA-256 values:

- Question: `69fb309b2db92286901cf00bbf5ef38d18d3c7bcd8540017b0bbe2ae99534e58`.
- Draft: `8b097f9d4c5b0e49790dbcb6fdabb7126c8a98eff157dee9a13eac8af6b89526`.
- Approved answer: `f6bbefc18aa7760d7c5002cb404142ac66d4bc3bb088b2aeb6b667bb69f4ef6a`.

The embedded approved draft is byte-identical to the saved complete revision 1.
The wrapper records the final `OK` immediately after the complete saved draft
was displayed; the earlier `1` selected the option and is not substituted for
that final approval. Stable message/thread URLs are explicitly unavailable.
Question/draft identities, revisions, absolute worktree and branch match.
The question baseline `44bc1e530`, draft-observed `c28e89ff8` and predecessor
bundle `885012b42` are ancestors of discovery HEAD `0f26a951e`. The runtime
machine is still exactly SHA-256
`04024174d88223e252e1d093eaee96c17d9f43d4d32bea5c41631017c9da208c`;
no relevant operational premise changed. The three validated files were staged
explicitly and committed together at `6b6cafea1`, then checked byte for byte
against that commit before consumption. Unapproved predecessor draft history
remains untracked and excluded.

Independent `spec_auditor` `ordinary_carrier_contract` returned CLEAN for the
exact addendum/receipt/task/index transcription: no additional scheduling,
failure, initialization or runtime-closure decision is inferred. This M0
record synchronization used one conformance reviewer, static exactness/link/
whitespace checks, and zero executable/performance measurements.

## Consumed scope

The [governing decision](../../notes/design/2026-10-16-initialization-order-global-effects.md)
now records option 1. The relative-order rule counts effects actually escaping
each initializer after its own handlers. A completely handled internal request
does not count; an effect escaping a handler arm or resumed computation does.
Effects reaching an automatic global consumer count before that consumer.
Declared permissions and nonempty static upper bounds do not prove occurrence.
The internal `ping 2` then `ping 1` example alone therefore does not violate
this ordering rule; this is no certificate of whole-source admission or scheduler
correctness.

The earlier global-handling-or-error rule remains. No detector, scheduler,
blanket dependency-first policy, extra uninitialized-reference behavior,
observable speculation, arbitrary global registry or old A/B publication law
is selected. Proofs and implementation keep their existing separate gates.
Only the observation decision is consumed here, without compiler/runtime edits
or executable checks. The primary assigns a constructive all-current-runtime
outward-event proof alongside an independent public-consumer/source-label audit.
Whole source initialization, materialization and production remain OPEN.
