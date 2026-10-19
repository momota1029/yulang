# R90 — Lambda body/result consumer at its actual source owner

Status: ACTIVE; primary-owned bounded source-to-proof investigation.  
Branch / baseline: `research/simple-sub-intrusion`, `271f6da0da7b6b43d911171348882df12e4839a6`.  
Parent: `R67-DIRECT-BODY-CHECK-1`, applying to `R68` and the original computation-forwarding preservation theorem §§1, 6–7. Preserve its original source domain, quantifiers, shared `xi=(nu,K,D)`, receiver/foreign-continuation obligations, and parent/evaluator A/B OPEN 0→0. R50 remains NOT_ADOPTED.

## Fixed question and success evidence

For the original retained-entry source

```yu
act io:
    our tick: int -> int

my forward (t:[io] int): [io] int -> [io] int = t
my outer (q:[io] int) = forward q
```

trace one original retained `forward` Lambda/body occurrence through the actual source owners and determine whether an existing selected source rule and its actual implementation consumer supply all of:

1. an independently formed Lambda challenge/domain from the actual retained formal and captures;
2. a body-checking target at the body occurrence, before whole-binding annotation checking;
3. the designated consumer for the same computation carrier/provider;
4. the body result, return/rebind, invocation and complete prefix/pending-observation evidence required by the source Lambda rule.

Start from the R67 owner `R67-DIRECT-BODY-CHECK-1`. Inspect the actual `Action::Lambda` and `Action::Annotation` consumer bodies in `crates/yu-solver/src/lib.rs`, then relate only their concrete inputs/outputs to the exact action producers in `candidate_source.rs` and formal registration in `candidate_call.rs`. Preserve the same occurrence, source root, formal, body endpoint, annotation occurrence, carrier/provider and original context. Keep written `p_t`, whole annotation `p_A`, and result annotation `p_R` distinct.

Success is either (A) a constructive bridge from actual source constructors through the selected source Lambda/checking rule to the exact local premise, with all of 1–4 supplied from independent owners before whole-annotation checking; or (B) an exact first missing premise at its authentic source owner, with a falsifier that would distinguish a real source rule from an implementation-only relation. Apply the result to R67 and state whether its bounded obstruction is discharged, refined to a smaller premise, or unchanged. A source trace alone is not a theorem and cannot close R67 or the original parent.

## Authority and dependency pins

Use only the selected source Generalize rule in `notes/design/2026-10-08-source-generalize-definition.md` and its proof, R67's frozen derivation, and the exact source pins below. R68 is an earlier candidate only; this R90 contract explicitly adds the previously excluded `lib.rs` consumer as a read-only input. No semantic amendment or new language rule is authorized.

```text
2300400e87d0a487225f207d414ac71fa4f21c6f80279fea4f793e43c7809aee  crates/yu-solver/src/lib.rs
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c  crates/yu-solver/src/candidate_source.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479  crates/yu-solver/src/candidate_call.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0  crates/yu-solver/src/candidate_effect.rs
0d9a9a8b98611a6f7e9897d3b242614ee36c4a724cfe5968eee536cb959e7bea  notes/theory/2026-10-19-r67-direct-lambda-checking.md
46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38  notes/design/2026-10-08-source-generalize-definition.md
e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240  notes/theory/2026-10-08-source-generalize-definition-and-proof.md
7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81  notes/design/2026-10-11-yulang-inference-top-level-principles.md
```

R67 is not rewritten. Do not import R68's excluded files as evidence without a revision and new pin. Current R67 hash and all R90 pins must still match at freeze and review.

## Method and falsifiers

Use a source-owner trace followed by a constructive source-rule derivation. For each constructor and consumer, write its exact occurrence-indexed input, output and scope. Distinguish a generated `Action` from a consumed action; distinguish a candidate endpoint/constraint from a source typing derivation; distinguish root annotation links from prior body checking. Test whether the annotation target or negative `p_A` evidence is needed to create the purported prior operand. Preserve pending/future observations, ordered suffixes, provider identity and same-carrier consumption.

Falsifiers include: importing native constraints as source premises; using successful annotation comparison to construct its own prior body target; treating root-level Lambda admission as designated body consumption; equating a static occurrence with each runtime request; identifying copied endpoints or carriers; using a value-only Return to discharge computation observations; or dropping any original parent quantifier, provider, scope, permission, capture, ordinary constraint, or annotation occurrence.

## Lanes, outputs, budget and stop

- Luna owns a bounded primary derivation and source-owner map, cap 600 seconds. Exact outputs: `notes/theory/2026-10-19-r90-lambda-consumer-owner.md` and `tasks/agent-loop/inbox/20261019-r90-proof.md`.
- No implementation write or test/build/CLI/probe is authorized. The owner audit has already inspected the separate `candidate_source.rs`, `candidate_effect.rs`, and `lib.rs` consumers. Unless the derivation identifies a proved invariant and an exact approved end-to-end slice, implementation remains WAITING and the handoff records `NO_SAFE_CODE_SLICE` with these owner-specific dependencies.
- Fresh independent compiler/source review only after the candidate is frozen, cap 240 seconds; it is not proof closure. No author reviews their own artifact. No Astra and no descendant spawning under this primary-owned envelope.
- Luna owns `tasks/agent-loop/current.json`, handoff intake, adjudication, review assignment, integration and Git. Do not edit existing inboxes, questions, tests, source, expected output, design authority or unrelated records.

Stop at the first source-owned rule that genuinely supplies the complete premise, or the first precise missing constructor input. Do not continue an equivalent effect-storage/fiber analysis after identifying the owner gap. Apply the finding to the original R67 parent immediately; keep it OPEN unless its original conclusion actually follows and receives fresh independent proof review.
