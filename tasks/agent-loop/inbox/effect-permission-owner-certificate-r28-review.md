# R28 source-only independent review, revision 1

Status: **REJECT** for the pre-compile source gate. This is Luna's durable
transcription of the read-only handoff returned by `/root/r28_review`; the
reviewer wrote no files. No compile, test, runtime, Lean, Lake, or checker gate
was run.

## Frozen identities

- Contract: `fa1a6f2e450169748e0696fb607963147a46cc4e6c464087cdefcacec383d89a`
- Schema R1: `fb46c1c031ee9132385c2170c22cbf8ea5eb27a8dc176ce0ba6356b7cf4a71ea`
- `machine.rs`: `015db9d7adf57b2c9ca628b5908c7c58f50c279b26b19cafb2f082ba33cec86a`
- `receiving.rs`: `632e9a23951d2791d4638400a5f93815bbb1c9831f388ddae4a8a0e806470ddb`
- `NativeCallbackGrantBridge.lean`: `7089b047821ed82e715b4230c47e36f5fec231bf431ec6d26501137f8a358c18`
- Read-only R26 overlay: `0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e`
- Rust handoff: `29e5dc84d04d92a64801b50c2cb748a666ac6d0078a078f0beae8c128dbb9616`
- Proof handoff: `074a9713eb0e8475bdf6ce43bf9deb0172159dc1e6a3b587f551e508e1c29f48`

The reviewer independently rechecked these hashes and the detached W baseline
`c9e315208cb04bcc4fe8c3595d929fb76538f1cd`.

## Findings

### BLOCKING: wrong handle type passed to `callback_grant`

At `receiving.rs:604`, `validate_callback_route_evidence` passes
`use_record.entry` (`CallbackEntryHandle`) as the first argument to
`callback_grant`. Its definition at `receiving.rs:895` requires
`CallbackUseHandle`; these are distinct newtypes (`receiving.rs:118,120`). The
test-only validator cannot type-check. Use the already authenticated use
handle; do not cast an entry ordinal into a use ordinal. Freeze new hashes and
obtain a new exact-hash review before compilation.

### Major: actual handler installation identity is omitted

`HandlerInstallation { occurrence, owner }` is defined at `machine.rs:273` and
authenticated at `machine.rs:2485`. The certificate record at `machine.rs:125`
retains a Catch source site but omits the installation occurrence. The emitter
at `machine.rs:4098` derives `handler_id` from `consumer_handler.occurrence`, a
source occurrence. Two dynamic installations at the same source occurrence can
therefore receive the same emitted handler identity. The selected route lacks
the native installation handle required to establish that this installed
delimiter consumed the request. Retain and serialize the actual installation
occurrence and its authentication context, separately from the Catch source
site, and join it to the selected Catch/arm.

### Major: authenticated observer and bound are absent from emitted evidence

`receiving.rs:568` records `observed_observer`; the callback JSON builder at
`machine.rs:4058` omits that value and the owning `next_observer` bound. The
Lean candidate at lines 110–119 requires the execution-table entry, observer,
and bound. The Rust validator at `receiving.rs:610–662` does not check the
observer against `next_observer`, while native `local_grant` rejects an
observation outside that bound at `receiving.rs:796`. Replacing the observation
with an out-of-bound observer is not distinguished by the emitted JSON.
Preserve the actual observation, observer, bound, execution-store projection,
and their joins to the query and selected Catch.

## Review scope and limits

Source instrumentation is mostly test-gated. The direct parameter Name checks
belong to `callback_entry_for_apply`, not `callback_grant`; callback and
companion identities remain separate; permission, request, execution and Catch
records remain distinct. The companion mutation targets are present and visibly
changed before validation; their rejection has not run. No production decision
change was found. `receipts/owner-certificate.json` does not exist.

The Lean file is an unchecked generic record model. Its `UseReady`, `PortReady`,
and `CatchReady` implications do not establish native extraction or native Grant
equivalence. No R28 theorem has kernel-checked printed types or an axiom audit.
Full History, original source soundness, symbolic/type-argument rows, RootComp,
principality, termination, and production remain OPEN.

Reviewer: `/root/r28_review`, registered `compiler_referee`, requested
`gpt-6.1-sol/medium`, observed routing UNKNOWN. Launch 2026-10-29 22:45:44 UTC;
conservative charge 180/1,200 seconds. Reads, searches, hashes, and Git
inspection only. No children, source edits, generated certificate, or live
processes. Writes stopped.
