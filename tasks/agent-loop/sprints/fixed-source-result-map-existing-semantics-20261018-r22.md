# R22 rev2 — Fixed-source result map from existing semantics

## Parent, baseline, and outcome

Original parent remains `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`,
with original quantifiers, source/native correspondence, principality, Call,
soundness and termination requirements unchanged. Parent is **OPEN / closure 0**.

Baseline: root-pushed R21 closeout `3436209db` on `research/simple-sub-intrusion`.
Reuse CLEAN R20 proof
(`notes/theory/2026-10-18-fieldbound-prefix-and-use-construction.md`, SHA
`1ab75dd2b5210068ce272de81e41ee42d38c57d41a3b8d193d11b4f1b3387ddd`) and the
R20 fixed `runtime_resume` result (18/18). R21 rev3 review certifies document
conformance only: fixed-source ResultMap remains OPEN, A is an unadopted
annotation-root proposal, and B is blocked on rooted capture traversal.

R22 has one parent-relevant target: derive `D0/D1/D2` for the fixed source from
its **existing** actual raw suffix, saved continuation, response substitution,
completion/return, actual arm final value, Catch slot-50 edge, and Install(g),
or refute the required value-origin claim with a concrete baseline-admitted
source. Do not add a missing `Orig` constructor to force D1, equate endpoints,
assume `A_decl` is identity, or use one execution returning 42 as universal
proof. If the source theorem holds but the candidate encoding cannot represent
it, state those separately. No R21 A/B rule is adopted in R22.

In parallel, add a strictly observational runtime trace for the exact saved
suffix/frame/value lineage so proof and implementation correspondence can be
checked. It may record facts already present in current runtime structures; it
must not alter constraint generation, source admission, handler choice, runtime
transitions, receipt conditions, or completed outcomes.

## Frozen dependencies

```text
fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46 tools/inference-playground/src/runtime/machine.rs
194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3 tools/inference-playground/src/runtime/continuation.rs
484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11 tools/inference-playground/src/runtime/program.rs
3902e5071d9d2bc8bede6cc03fe74e224cf12627de7bcfc147ec850b9fd560bd tools/inference-playground/tests/runtime_resume.rs
f97d6ca85b60a5eec8bc20d98fcdf75904551eaacbdc5084026289362681676a notes/design/2026-10-18-field-root-incidence-bridge-options.md
1e85ae26d7caf678a28ec2cafe59ca4c8f6186a9f07de6b00d5f426cf2efb699 notes/theory/2026-10-18-field-root-incidence-bridge-soundness.md
a881422001c4d3544e714a17f78681dc44e2360b204b6c362ea83a542908489e notes/theory/2026-10-18-field-root-incidence-source-falsifiers.md
```

Dependency drift returns to Luna. The R21 option and falsifier artifacts are
read-only. No solver or HIR files are leased.

## Productive lanes and leases

### A. Existing-source derivation — Sol/high, 900 seconds

Writes only:

- `notes/theory/2026-10-18-fixed-source-result-map-existing-semantics.md`
- `tasks/agent-loop/inbox/20261018-fixed-source-result-map-proof.md`

Trace one exact fixed source through the existing source semantics: authenticated
request/capture boundary, ordered saved suffix, exact continuation binder and
response substitution, actual completion/return/provider view, arm final value,
Catch result and Install(g). Give source rule/constructor and native owner for
each leg. Derive a value-origin lineage for every response/state allowed by the
fixed source assumptions; do not generalize beyond that source. Address actual
`original` and typed port identities without equating them. If some leg depends
on an absent rule or is not source-determined, leave that leg OPEN. Distinguish
a source-level derivation from whether candidate `Orig` can encode it. No code,
tests, or new inference rule.

### B. Independent source falsification — researcher, 600 seconds

Writes only:

- `notes/theory/2026-10-18-fixed-source-result-map-source-falsifiers.md`
- `tasks/agent-loop/inbox/20261018-fixed-source-result-map-falsifiers.md`

Independently compare response returned, discarded and replaced by another
provider. Check the fixed specimen's exact suffix and actual arm final-value
route. A counterexample must demonstrate baseline parse/HIR/candidate admission
and an actual result/value-origin basis; R20's receipt covers only the exact
fixed specimen and cannot be reused for modified variants. Static or hypothetical
variants remain candidates, not source counterexamples. No source edits, tests,
or builds; identify a minimal exact Luna-owned check if admission evidence is
needed.

### C. Nonsemantic suffix-provenance trace — Luna/high, 600 seconds

Exact code lease, only after Luna freezes the observation plan in this contract:

- `tools/inference-playground/src/runtime/machine.rs`
- `tools/inference-playground/src/runtime/continuation.rs`
- `tools/inference-playground/tests/runtime_resume.rs`
- `tasks/agent-loop/inbox/20261018-fixed-source-suffix-provenance.md`

Trace current runtime facts only: saved `ResumeTemplate` node/frame shape and
source sites, template entry/hole substitution, actual response `ValueHandle`
and `SourceSite`, active execution owner/view transitions, actual resumed
return value/source site, selected Catch arm, arm/body result and final completed
value. Preserve order and exact handles/occurrences. Bound the trace size. An
inspection method may expose bounded debug strings from the already re-exported
`Machine`; do not modify `RuntimeEvidence`, `OperationV1RuntimeReceipt`, or
`operation_v1_runtime_receipt` predicates. No new source inference, capture
semantics, handler/runtime transitions, source admission, or endpoint equations.
If an exact value/site/owner is not present in the runtime, report UNKNOWN rather
than synthesizing it. The bounded event buffer holds at most 128 entries and
records an explicit truncation count; no unbounded trace growth. Each event
includes the observed event kind, actual `SourceSite` root/occurrence/range when
available, actual value/template/node handle, and actual `ExecutionOwner`/view
when available. Required observed points are: captured `ResumeTemplate` node
and saved frame/source-site sequence; template/hole entry and the substituted
response handle/source site; actual resumed `State::Return` value/source site;
actual selected Catch arm; actual arm/body final value site; and completed
value site. Preserve event order. A read-only debug-string method on the already
re-exported `Machine` may expose this buffer to the integration test without
editing `runtime/mod.rs`, `lib.rs`, `RuntimeEvidence`, or receipt structures.
`continuation.rs` may expose only a bounded rendering of the actual immutable
node/frame structure. Test comparison must separately label static source
occurrence identity and dynamic value-handle identity; neither alone implies a
typed field relation. For falsifier cases, test code may assert existing
parse/HIR/candidate admission and record actual outcome only; it may not alter
admission or receipt policy. The R20 fixed specimen's baseline source and
static receipt assertions remain intact. Do not run a test before independent
review of frozen trace/code delta.

## Review, focused verification, and resources

A non-author compiler referee reviews frozen trace/code and proof/falsifier
packets for source correspondence, value identity, capture ordering, bounded
observation, unchanged receipts/admission/transitions, and counterexample
validity. No author self-certification. Luna owns all Cargo processes, one at a
time. After CLEAN only, run the exact target once:

```text
cargo test -p yu-playground --test runtime_resume
```

Revision 1's 2700-second cap is fully charged. Revision 2 adds one bounded
review-repair continuation of 900 seconds, bringing the sprint cap to 3600,
fully reserved/charged: prior proof 900 + research 600 + trace authoring 600 +
initial review 360 + repair 360 + delta review 240 + one focused run and
integration 300. Astra 0; no R21 carryover. The added envelope only repairs
the two reviewed observational-trace findings below; it does not reopen the
source proof, widen source admission, or authorize a semantic rule.

The exact repair lease remains the same three runtime/test paths and the same
trace handoff. Repair must bind arm-result observations to actual arm lifecycle:
record all nested tail Catch arms that complete at one return boundary, and
retire or preserve observers correctly when a request unwinds, is abandoned,
or is captured for later resumption. It must not insert semantic frames or
change evaluation transitions. Render existing view/receipt handles at every
observation point where those handles are present; retain `UNKNOWN` only when
the runtime truly lacks the identity. Add focused assertions for nested tail
Catch and an escaping/captured request lifecycle while preserving all R20
assertions. Freeze code and handoff for independent delta review. Only after
CLEAN, run `cargo test -p yu-playground --test runtime_resume` once. If CLEAN
cannot be reached within the added envelope, retain the findings and leave the
trace provisional.

`python3 tools/agent_sprint.py check` is static state evidence, not proof or
independent review.

## Success and stop conditions

Success requires either (i) actual existing-source derivation closes the fixed
source ResultMap leg without a new rule, or (ii) a concrete baseline-admitted
fixed-source counterexample falsifies the required result-origin claim. A trace
alone, candidate source, newly proposed rule, or repeating that the current
candidate encoding lacks an `Orig` constructor is not success.

Stop at the first genuine missing source rule, counterexample, pin drift, trace
that would alter evaluation/receipt semantics, failed focused target, or cap.
Keep R21 semantic options unadopted until separately selected and reviewed.
Original parent conditions close only when its unchanged source/native
quantifiers and proof gates are discharged; R22's bounded result never weakens
them. Commit/push root-integrated checkpoints frequently and never stage
quarantined paths.
