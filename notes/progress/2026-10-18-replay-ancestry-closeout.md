# Replay ancestry authentication sprint closeout

Sprint `npair-replay-ancestry-authentication-20261018`, rev1, closed
REVIEWED-PARTIAL. Original parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`
remains OPEN; original conditions closed 0.

## Proof

The conditional diagnostic ancestry criterion is recorded in
`notes/theory/2026-10-18-replay-ancestry-authentication.md` SHA
`00603a98b9f66eb71c61c0fe80e8812ff059c6cde54abd2d91e02036674381f6` and
handoff SHA `103dc19eee6e0c961e0e4cfa2bf6d43cff2852bacdab7a9d818a2c424a6bb433`.
Fresh proof/spec review was CLEAN. It fixes a Replay row first, then requires
exact fibers, the captured/imported snapshot, a unique owned FreshUse witness,
supported root transitions, and four typed FunctionPort records. It makes no
claim that arbitrary Derived rewrites are semantically valid. Fixture runtime,
consumer execution, fixed-c `At(D,c,delta)`, complete dependent transport, and
universal P3/P4 remain open.

## Implementation review

Frozen implementation snapshot was committed for research preservation at
`c89e73ad0`; it remains unapproved. Hashes:

- `candidate_context.rs`: `cde5c7368a038d77793d2d8b07e0beb400c33b83d4dd0cd689076d641ee788fb`
- `candidate_scheme.rs`: `1b5da9c8b34a53db04875294e03b5d03997abd78fc43145cce0742ad4a72ef03`
- `shadow_apply.rs`: `683928cc71f828b3536950911b8d20d5c141415300555c2271d4b790ac8d7e65`
- `candidate_graph_call.rs`: `01dbaef3b6d6b8f7a943fe627b64ad7fa7822e5ea7f04437b9ef390f4e8eec7e`
- example: `e4c1bec2a41accfe09f664d5992b2575ce78b855c3ff622f08eeb6de8765e3d3`
- progress: `4889d6318f1286af52ef6aeae24e5f0cb92c053eb30b89412916b8cf1241b92a`
- implementation handoff: `ad55200421ff3925f2d9d608dc38603380851e033831b417d7ab8142903ea652`

Compiler review BLOCKING: the implementation conflates the source relation,
copied FreshUse bound and Replay child, then rejects the intended path as
multiple incoming dependencies. It locates FunctionPorts under Replay upper
rather than the actual comparison Replay child/consumer, and does not link
mapped terms to their actual child endpoints or stamp/protect transformers. It
does not authenticate the captured evidence snapshot, imported antecedent,
restored fiber or Replay recipe. MAJOR: intermediate scoped-flow equations
are unchecked and falsifiers change metadata IDs rather than the underlying
evidence. The swap helper fix is sound and included by the helper-filter
command. Two-result integer propagation is asserted. No tests/builds/runtime
ran; `git diff --check` passed. All reviewer notes are pinned in this receipt;
reviewer STOPPED.

Conservative resources: 1680/2400s charged; 720s expired without rollover.
Astra0. Next exact task is end-to-end identity/fiber/consumer endpoint
correspondence, with focused authentic and falsifying tests, then fresh review
before any of the three one-shot runtime commands.
