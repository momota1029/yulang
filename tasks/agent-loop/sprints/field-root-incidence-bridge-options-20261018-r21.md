# R21 — Field-root incidence bridge options

## Parent, baseline, and fixed outcome

Original parent remains `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`,
with original quantifiers, source/native domain, principality, Call, soundness,
and termination conditions unchanged. Parent starts **OPEN / closure 0**.

Baseline commit: `d2ff62845` on `research/simple-sub-intrusion`. Reuse the
CLEAN-reviewed R20 proof at
`notes/theory/2026-10-18-fieldbound-prefix-and-use-construction.md` (SHA-256
`1ab75dd2b5210068ce272de81e41ee42d38c57d41a3b8d193d11b4f1b3387ddd`) and
R6 source design (`276979eccec49396c6799b96ca1e0277c6108dc2fd1fe487a52e4565cff6ed54`).
Runtime gate is CLEAN and its exact focused target passed 18/18 in R20; reuse as
an implementation dependency only, not theorem closure.

R20's exact obstruction is missing typed incidence between (1) the initializer
and callback field member `m0` and the successful response annotation's exposed
root `R_response`, and (2) actual response FreshUse `S`, its continuation and
resumption result, Catch root, and the exact installed `g`. Prefix preparation
alone cannot supply either incidence. Existing rules do not justify endpoint
equalities such as `L=A+` or `S=R_ping`.

Fixed R21 outcome: produce two fully specified bridge-rule options for these
incidences, an independent soundness/falsifier audit, and a source-to-native
implementation contract; obtain fresh independent review of all three packets.
No option becomes authoritative, no semantics or solver code is changed, and no
original parent condition closes in this sprint. Finish with a concrete choice
for the user, including compatibility and soundness tradeoffs.

## Exact pins

```text
66b8f88bad86755c2716cfa7e9c35eabc7031d408b774358ca72446db2b3180c crates/yu-solver/src/candidate_source.rs
6112343b4014c67dcb7d814a46412b3af3e1d12183924e891df4817a59f58da0 crates/yu-solver/src/candidate_effect.rs
42f89dcf5fa6d7095db1e220c89308a2a35f4e74b05c3e8821d4fb2e3e32b0ca crates/yu-solver/src/candidate_context.rs
e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479 crates/yu-solver/src/candidate_call.rs
03b44d0f8280c1ae79f66b5528f1bd0b0ffebac46b312ef7ffce605f702f48dd crates/yu-solver/src/candidate_scheme.rs
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb crates/yu-solver/src/shadow_apply.rs
fc0d948d884a406746066f3df8db257d5c6686505166b330bef839a9b9e2f35d crates/yu-solver/src/candidate_extrusion.rs
```

Any pin drift goes back to Luna. No worker writes source/solver code in R21.

## Parallel lanes and exact leases

### A. Bridge-rule construction — Sol/high, 900 seconds

Writes only:

- `notes/design/2026-10-18-field-root-incidence-bridge-options.md`
- `tasks/agent-loop/inbox/20261018-field-root-bridge-proof.md`

Specify exactly two options:

- **A — retained successful annotation derivation:** retain the exact successful
  local annotation comparison and exact initializer/field provenance, then
  derive its incidence with the exposed response root.
- **B — independent response presentation:** treat the response annotation as
  an independently exposed presentation, then construct field realization
  through the actual FreshUse, continuation source interface, and complete
  result map.

For each, give introduction/elimination rules, owners, scope/position, required
premises, conflict and publication conditions, and the actual resumption/Catch
case. Do not place desired incidence among the premises. State what each rule
adds beyond existing rules, what it preserves, and whether it can derive both
missing incidences without endpoint equality. No implementation edits.

### B. Independent falsification and soundness — researcher, 600 seconds

Writes only:

- `notes/theory/2026-10-18-field-root-incidence-bridge-soundness.md`
- `notes/theory/2026-10-18-field-root-incidence-source-falsifiers.md`
- `tasks/agent-loop/inbox/20261018-field-root-bridge-falsifiers.md`

Attack both options using (i) equal annotations with different initializers or
callback members; (ii) continuation returns response, discards it, or returns a
different provider; (iii) two distinct FreshUses; (iv) shared anchors; and (v)
scope changes. Separate existing-source-admitted cases, candidate test
constructions, and hypothetical contexts. Do not call a hypothetical context a
source counterexample. Identify soundness, principality, Call, and termination
obligations; reject rules that accept another initializer/use's field, fabricate
result incidence after discarding the response, or strengthen a lower bound
without source evidence. No implementation edits.

### C. Implementation contract — Luna/high, 480 seconds

Writes only:

- `notes/design/2026-10-18-field-root-incidence-implementation-contract.md`
- `tasks/agent-loop/inbox/20261018-field-root-bridge-implementation.md`

For each rule option, map producer/payload/consumer to
`construct_candidate_local_annotation`, `admit_candidate_fact`, Catch
construction, Graph capture, FreshUse mapping, and exact use edge/drain/ack.
Compare source ownership, retained typed coordinates, actual edge construction,
rollback, conflict/publication, diagnostics, acceptance boundary, and tests.
Label all code as unimplemented. Do not write solver/HIR/runtime code or change
receipts, tests, theorem premises, or language semantics.

## Review, integration, and resources

A non-author spec/compiler reviewer independently reviews all three frozen
packets for rule/source fidelity, cross-lane consistency, falsifiers and
implementation correspondence. No author self-certification. Freeze hashes
before review. Review budget is 480 seconds; Luna integration and exact-path
checks use 240 seconds. Total cap 2700 seconds, fully charged: proof 900 +
research 600 + implementation contract 480 + independent review 480 +
integration 240. Astra 0; no carryover from R20.

Only Luna updates sprint state, assigns reviewers, integrates and performs Git.
Run the compact-state static check after state edits. Commit/push coherent
reviewed checkpoints frequently; never stage quarantined paths. No cargo test is
authorized because R21 changes only research/design documents.

## Stop and completion

Stop at the cap, dependency drift, concrete counterexample, or a semantic
question whose answer cannot be represented faithfully in the two options.
R21 completes only when all three exact outputs are frozen and independently
reviewed, with the choice and its original-theorem consequences stated plainly.
A proposal, proof under an unadopted rule, or passing test closes **zero**
original parent conditions. The parent theorem remains OPEN until its unchanged
source/native quantifiers and all proof gates are discharged.
