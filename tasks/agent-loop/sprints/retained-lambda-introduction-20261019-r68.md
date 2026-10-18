# Sprint R68 — retained-entry Lambda introduction for the original operand

Status: CANDIDATE only. No work is granted until Luna verifies this exact
manifest and baseline, obtains the dispatcher start check, reconciles all
identities/leases, freezes this contract and activates it in `current.json`.

Branch / candidate baseline: `research/simple-sub-intrusion` /
`f49f797a0c04fe02a68b63bff9ff3e254ba6002b`. Primary: `/root`.
Proposed session: `current-conversation-2026-10-19-r68`.
Parent: original computation-forwarding preservation §§1,6–7; unchanged source
domain and quantifiers; Simple-sub A/B OPEN 0→0; R50 NOT ADOPTED.
Upstream OPEN items: `R65-CURRENT-OPERAND-1`,
`R66-LAMBDA-RESULT-STAGE-1`, and R67's bounded local premise
`R67-DIRECT-BODY-CHECK-1`; downstream R64/R61 remain OPEN.

## Fixed source and outcome

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

Attempt a constructive **retained-entry Lambda introduction** at the original
`forward` binding. Combine the selected source-interface constructors with the
contextual Function-membership and immutable-input laws to derive, in one
original joint context, the symbolic Lambda interface and the complete
body/consumer/invocation evidence needed to supply the ordinary typed operand
to R65. The formal is a retained computation entry: preserve the same
independently admitted whole carrier at `t`; prove the resolved `Name(t)` body
and its actual designated consumption, then prove the complete invocation and
all required observations for that same original callable/interface.

Construct each challenge from independently valid compatible context,
carrier contract, receipt and typed-path inputs before examining the Lambda's
acceptance or observations. Prove acceptance and observation safety for the
same actual provider and carrier. Retain initial and administrative states,
every finite completed or pending prefix, typed responses, raw handles,
ordered suffixes, returned-provider/future obligations and all original hard
constraints. If the selected laws do not derive the full operand, identify the
first genuine missing constructor or semantic premise at its owner.

The source-interface formation theorem is structural: it constructs typed
slots and inclusions from an authentic source derivation. Do not promote those
slots into callable membership, challenge admission, invocation safety,
coverage or a completed Lambda proof. The Call semantic-input theorem
eliminates an already genuine Function member; it cannot prove membership of
the newly constructed `forward` closure by assuming that premise. The
two-closure theorem for `my f x=g; my g y=f` has a different exact scope and
cannot be generalized to this Lambda. Result-A's unannotated Lambda equation
cannot replace the missing body-checking or introduction premise.

Preserve the original `I,d,L,t,n`, provider, formal and whole/result
annotation occurrences `p_t/p_A/p_R`, open incoming `E_t`, formal-only
permissions, captures, ordinary constraints, source scopes, result evidence
and typed-substitution dependencies. All local choices and alternatives stay
in one joint source context; do not solve the Lambda separately, assume a
completed `xi`, choose witnesses after solving, borrow `p_t` permission for
`p_A`, erase the whole annotation, identify an interior operand with the final
root, or infer source meaning from native constraints.

Success is either a direct source-rule derivation of the completed operand
and prior evidence at the original boundary, or the first authentic
unsupported local premise. This does not derive all of `p_A`, R64/R61
correspondence, actual `Q`, `Sol_nat`, full `Corr`, production admission, or a
new semantic decision.

## Method and falsifiers

**Constructive proof, Sol/high:** instantiate the original formal and resolved
Name, build the retained-entry source interface using the selected
source-construction theorem, and establish the exact independently admitted
Function challenges before proving actual callable acceptance. For every such
challenge, derive the same-carrier body consumer, complete invocation result
and all finite prefix/pending observations with their original scopes and
evidence. Connect this semantic derivation to the source Lambda checking and
result constructors, then return the completed typed operand and prior
evidence to R65's actual owner. State every independent hypothesis; do not
hide the missing source rule in an “independently typed operand” assumption.

**Complementary challenge attack, Sol/medium:** attack whether challenge
formation is genuinely independent of actual-callee acceptance, whether the
source interface constructor only preserves a record rather than introduces
semantic membership, and whether pending prefixes, retained carrier,
designated consumer and invocation evidence follow without assuming body
safety. Seek an actual premise mismatch or confirm the precise first gap.

**Luna/high owner map:** trace source formal/Name/Lambda/result/consumer and
the outer call through the pinned HIR and candidate owners. Identify exactly
what semantic and typed evidence each constructor receives/produces; retain
both negative-concrete `p_A` guards. No compiler edit. Record whether the
source/native owners justify any code slice; expect `NO_SAFE_CODE_SLICE`
unless this proof supplies the missing invariant and correspondence.

Falsifiers include: using actual-U acceptance to form the challenge; assuming
the Lambda is already a member of its proposed Function interface; using
successful Function checking to construct that same interface; replacing the
current closure proof with the exact two-root recursive constructor theorem;
dropping zero-step/pending/future observations or result/provider evidence;
assuming only total Return; using structural interface slots as semantic
membership; importing a post-solve witness, Result-A equation, native
endpoint/comparison or `Q` success as a source premise; or losing any original
provider, scope, permission, capture, ordinary constraint or annotation
occurrence.

## Lanes, outputs and resource envelope

- Constructive retained-entry introduction proof, Sol/high, 900s:
  `notes/theory/2026-10-19-r68-retained-lambda-introduction.md` and
  `tasks/agent-loop/inbox/20261019-r68-proof.md`.
- Complementary challenge/body-safety attack, Sol/medium, 300s:
  `notes/progress/2026-10-19-r68-introduction-counter-reading.md` and
  `tasks/agent-loop/inbox/20261019-r68-research.md`.
- Luna/high source/native owner map, 500s:
  `notes/progress/2026-10-19-r68-retained-entry-owners.md` and
  `tasks/agent-loop/inbox/20261019-r68-implementation.md`.
- Fresh independent compiler and spec reviews, 200s each, after every author
  output is frozen.
- Luna integration and durable closeout, 300s:
  `notes/progress/2026-10-19-r68-closeout.md`; Luna owns
  `tasks/agent-loop/current.json` and shared task-record synchronization.

Total 2,400s; Astra 0; no carryover. No implementation lane is authorized.
No compiler, test, expected-output, semantic, build, execution, probe,
instrumentation, measurement or production change; no test runs. Authors do
not start descendants, expand leases, edit shared state or use Git. Reviewers
are read-only. Luna alone adjudicates, updates shared state, stages explicit
paths and commits/pushes.

## Required operational boundaries

The R67 closeout confirms the previous exact result and remains distinct from
parent closure. The selected construction, semantic-input and source
Generalize claims below are pinned evidence only within their declared
scopes. `simultaneous-immutable-root-introduction.md` is a selected local
candidate theorem for exactly two mutually recursive immutable closures; this
packet may use it only as a contrasting scope boundary, never as a rule for
`forward`. Additional semantic authority must return to Luna before any
read/use. Draft laws do not become authoritative through review or use.

Required startup/governance reads: `AGENTS.md`, `AGENTS.pre-sprint.md`, rules
`agent-orchestration.md`, `research-lab.md`, `design-authority.md`,
`orchestration-budget.md`, sprint decision
`notes/design/2026-10-16-goal-driven-sprints.md`, skills `yulang-sprint` and
`yulang-proofs`, `tasks/agent-loop/current.json`, and
`tasks/agent-loop/README.md`. These are operational context, not source proof
evidence. For semantic evidence, authors/reviewers use only this frozen direct
manifest. The compiler file `crates/yu-solver/src/lib.rs` is excluded; any need
for it requires a new dependency and review snapshot.

## Frozen direct dependency manifest

Every file below must match its SHA-256 at activation, author freeze and
independent review. This pins R67's reviewed outputs, the selected source
interface construction and its selecting/review records, the selected
contextual membership and semantic-input clauses, the source construction and
Generalize rules, and the actual HIR/candidate call sites for owner mapping.

```text
00ee065651f9440a94321469b34543011d63efeec0b25a06e5d00b41ff2f1e49  notes/progress/2026-10-19-r67-closeout.md
6e5a248634eab018f4020a416ca5fac1124452ecc7cb3ad789ffa6c440be349c  tasks/agent-loop/sprints/direct-lambda-checking-20261019-r67.md
0d9a9a8b98611a6f7e9897d3b242614ee36c4a724cfe5968eee536cb959e7bea  notes/theory/2026-10-19-r67-direct-lambda-checking.md
3d27138f0448a25911d61af672b70da2b4be0b66ccfcbac5dce6f2f6fefe4c6a  tasks/agent-loop/inbox/20261019-r67-proof.md
6769913e4cf53a6e6ac84f4d0f4eea9b85ab44c45b34e39a171073ba777872d0  notes/progress/2026-10-19-r67-checking-counter-reading.md
f13f9cf426d6f3213098e36d557f7903cf2a47e32ca81afc4bd049b4f53c1a19  tasks/agent-loop/inbox/20261019-r67-research.md
41d9278a4a3b7a8adb4ff19a0a05df2c2f0c7812d9c018cbab3ff5d81ecf5a1b  notes/progress/2026-10-19-r67-lambda-operand-owners.md
21045f1a23dcc570fca59bcc8f5909a87467e0ef947e77c9dbe5b235df4d6c37  tasks/agent-loop/inbox/20261019-r67-implementation.md
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c  notes/design/2026-10-08-call-source-interface-definition.md
278034197a90eab6e62a073545c09dd14415a0353f58aa3b3cc122a6af945d98  notes/theory/2026-10-08-call-source-interface-construction.md
b679ebc836cc3691854a243444595e5a8f35116a0766503886eebc65a1eb07c4  notes/progress/2026-10-08-call-interface-admission-review.md
0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0  notes/design/2026-10-08-contextual-function-membership-definition.md
fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a  notes/theory/2026-10-08-call-semantic-input-realization.md
a5efa7056b12f931892548ecf3366d66156627ec44577c99d20ca48596438ae6  notes/theory/2026-10-08-simultaneous-immutable-root-introduction.md
1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186  notes/design/2026-10-05-source-contracts-and-common-allowance.md
9b63603890cd522ec80ef81e6208c52acdb1f09ab0a847a9b51368a8f563acf3  questions/2026-10-05-production-function-inlet-context-domain/approved-answer.md
4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1  notes/design/2026-10-05-inferred-function-call-views.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
f7c1b1eb23acb33ab98487097ab67617e1af84964b012874b1c951a8805dd9f6  notes/theory/2026-10-07-call-input-construction-proof.md
eab807e2994d6f3f71987b9fc89592c4ac69fbc95c3eaf1b637b1802632b8f49  notes/progress/2026-10-07-source-constructor-completion-review.md
7766aff08cedde1ebc796b8927cd1d44f459df72a632e0c0d35d4bfcd28d335e  notes/theory/2026-10-15-computation-formal-permission-construction.md
71326de0897159343797d6aec083860ee0f57a1bc04f9c4ae77e579ea0ba5992  notes/design/2026-10-02-source-result-synthesis-choice.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f  crates/yu-hir/src/module/source_annotation.rs
ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5  crates/yu-hir/src/module/local_source.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
```
