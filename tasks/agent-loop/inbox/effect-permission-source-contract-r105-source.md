# R105 source-contract handoff

Sprint / contract: `effect-permission-source-contract-20261101-r105`,
revision 1; frozen content hash is reported with the submission.
Assignment: R105 source-contract lane; handoff revision 1.
Parent: original Yulang inference/source soundness and effect-hygiene claims;
source domain and quantifiers unchanged.

## Runtime, lease and result

Requested role/model/effort: `implementer`, Luna/high. Observed model/effort:
UNKNOWN. Worker identity: `/root/r105_source_contract`; actual launch/session
receipt: UNKNOWN. No descendants.

Outcome class: source-native evidence / exact obstruction. No Rust test was
added. The source mismatch hypothesis survives static source inspection, but a
corrected path has not been shown to pass the ordinary admission route. The
R104 test helper creates HIR and a candidate-mode batch directly; it does not
call `CandidateInference::solve`. The authorized Cargo call is conditional on
a fresh independent review of a new candidate, so no test/build command was run.

## Frozen inputs and hashes

- Contract: `tasks/agent-loop/sprints/effect-permission-source-contract-20261101-r105.md`
  — SHA-256 `7285a5d8cb6ca8d39c8f0427278c633ecccaf12d8591e9109825c7afce162e4d`.
- Governing annotation policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
  — SHA-256 `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18`.
- R104 outcome: `tasks/agent-loop/history/effect-permission-source-causality-20261101-r104-outcome.md`
  — read as source observation history.
- R104 source handoff: `tasks/agent-loop/inbox/effect-permission-source-causality-r104-source.md`
  — SHA-256 `4a4227fb6ca8cbefa3240cbec4b4fd485f3583750816827338b0717e0dfed5d5`.
- `crates/yu-solver/src/candidate_effect.rs` —
  `fab53f41cba94da6ada8850ae99b4ab03a7bfce46ff8f71306dc1b77ade73cb5`.
- `crates/yu-solver/src/candidate_source.rs` —
  `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`.
- `crates/yu-solver/src/candidate_scheme.rs` —
  `4494ba879a05f90767779e12c9ca8e1364f2203f2f60eb63239a544c0d0da470`.
- `crates/yu-solver/src/shadow_apply.rs` —
  `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f`.

## Source-contract adjudication

The named-header branch in `candidate_source.rs` (around line 2184) constructs
`Action::Annotation` with the endpoint and value position of the named group's
`terminal_body`, then separately links the outer Lambda to the definition root.
The source comment states the annotation is the result annotation of the
curried function. For R104's fixture, the terminal body is `pure`, where
`pure x = 1`; its argument type is unconstrained and its result is `Int`, giving
shape `α -> Int`. The annotation supplied to that terminal body has shape
`(Int -> ['e] Int) -> (Int -> ['e] Int)`. The two value shapes differ, so the
named result annotation does not match this terminal body's source type. This
is consistent with the pre-existing
`IncompatibleValue { lower: Int, upper: Function }` at root execution; the R104
trace independently reports that late `E` adds no error.

The ordinary source route is `CandidateInference::solve` in `shadow_apply.rs`;
its solve path calls `candidate_source::preflight_with_imports_and_roles` for
each retained local source. The R104 helper `make_session_with_file` does not
call that route. Static preflight inspection shows only shape/feature checks
for annotation trees; it is not a body-versus-annotation type check. Therefore
there is no R104 ordinary-preflight receipt, and this packet does not claim the
failing fixture was admitted by that route. A candidate replacement such as a
terminal local function `my apply (g: int -> ['e] int) = g; apply` appears to
have the required function-to-function shape, but remains an unvalidated
candidate. No source test established that the exact source is accepted and
that the returned Support survives capture, fresh use and the consumer.

The source admission discriminator needed next is an exact test-owned
`CandidateInference::solve` call on the corrected source, with the original
ordinary source domain. It must retain the annotation result, returned
function, captured Support, fresh-use remap and actual consumer path. Review of
that candidate must precede the one authorized Cargo call. If that check
rejects the fixture, preserve the rejection as source evidence and do not
weaken diagnostics or source-domain expectations.

## Four protected R104 failures and current owner evidence

1. **Shared-tail (`candidate_effect.rs:4986`).** The ordinary source constructor
   is the named-header annotation action in `candidate_source.rs`; it annotates
   the terminal body while retaining the outer Lambda. The current terminal
   body has the wrong value shape. The reported incompatibility predates the
   late-`E` contribution, so this failure does not locate a late propagation or
   annotation-permission omission. Source admission and a corrected end-to-end
   path remain unverified.
2. **Unequal transport (`candidate_effect.rs:3920`).** The run recorded only
   identity representative pairs and no `ParentWrite`. There is no authentic
   unequal source-to-capture transport in this evidence. Once a real source-
   induced representative transition exists, the first owner to inspect is
   capture allocation/canonicalization (`Capture::intern` and
   `canonical_effect` in `candidate_scheme`); the `r != q` assertion concerns
   that allocation-to-capture transition. `FreshUse` row remapping is a
   separate later obligation. `candidate_intrusion` parent activation or
   representative mutation has no observed event to explain here. No omission
   is established.
3. **Recursive consumer (`candidate_effect.rs:3943`).** The original recursive
   `f pair` source returns no effect forms. The separately tested pair-returning
   provider does create Support, but is not the original consumer path. This
   comparison does not determine whether the difference arises in source
   production, projection/application, capture/export, or consumer residual
   handling. No consumer-side omission is established; provider completeness
   and the original consumer residual remain open.
4. **Fresh-use Support (`candidate_effect.rs:5807`).** The live source session
   has Support bounds, while the captured templates have no Support node. Thus
   this observation does not show loss inside `FreshUse` remapping, which maps
   existing captured `EffectOperand` nodes. Live Support alone does not prove
   that the Support is reachable through a capturable path; capture also stops
   at borrowed rows. The source-to-template cause remains unlocalized. The
   original `.all` assertion remains failing; no remapping repair is authorized
   by this evidence.

## Parent application, TODO and boundary

Parent application: reject the claim that R104 established an owner-local
solver omission. Reuse the prior source traces only for the reported
before/after diagnostics, identity-only representatives, absent recursive
consumer effect forms and live-versus-captured Support inventory.

Exact next TODO for Luna/source owner: admit one correctly shaped replacement
through `CandidateInference::solve`, then preserve the complete source
annotation -> terminal returned function -> capture -> fresh use -> actual
consumer chain in one separately named `candidate_effect.rs` test. The falsifier
is ordinary source rejection, an incorrect terminal type, or a missing
source-attributed Support path. Keep every R104 fixture/assertion unchanged.
No candidate code or test output exists yet.

No semantics, expected outputs, diagnostics, source domains, production code or
other owner's files were changed. No disposable scratch/generated output was
created. No independent review or Cargo call was performed. All four parent
gates and the original source/native, A/B, effect-hygiene and production
obligations remain OPEN. Worker writes are stopped after this handoff.
