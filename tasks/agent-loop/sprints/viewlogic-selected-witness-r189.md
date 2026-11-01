# R189 — derive admission for the solver-selected ViewLogic witness

Status: proposed for bounded admission by the primary. Objective remains the
mathematical Yulang type/effect inference guarantee for unchanged source rules.

## Parent-linked target

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`
(`Contracts.lean:128–130`):

```text
∀ s x d a, supported s → generates s x d → solves d a →
  ∃ e, sourceJudgment s x e ∧ sameScoped s x e a.
```

For the unannotated App at `(q,f,arg)`, derive the outer
`Judgment.existsE` admission premise for the ViewLogic witness selected by the
same satisfying assignment `a` and original telescope `Δ`. The exact target
is:

```text
actual source generation + solves d a
→ choose z_a from this very assignment's ViewLogic binder
→ construct an independent raw domain/readout D_q(E,Δ), decode_q
→ k.admitted E ⟨q,.viewLogic,0⟩ (decode_q E z_a).
```

The source constructor consuming this is
`OriginalSourceGeneration.Judgment.existsE:751–754`, with
`Kernel.admitted:672` and formula use at `847–848`. This packet targets only
that App sub-obligation. It does not close the whole App case, parent theorem,
all-constructor soundness, principality, termination or source coverage.

## Method and exact boundaries

Construct the raw ViewLogic domain and readout independently of source
admission success. Extract `z_a` from the actual satisfying assignment; do
not choose a different witness, telescope, environment or shared state.
Interpret the actual generated formation clauses for this occurrence and
derive admission of this selected decoded value.

Do **not** require the stronger
`∀ z ∈ D_q(E,Δ), admitted(decode_q z)` unless an already pinned governing
equation makes that universal property necessary for the original binder.
Do not add admission as a generated constraint, define `D_q` by the desired
admission, assume `WellFormed → admitted`, assume complete C0 or the desired
source judgment, or turn the target into a conditional theorem. `sourceRules`
and `Build` remain the target side, not definitions of `generates`/`solves`.

If no concrete generated formation clause supplies the admission derivation,
stop at its exact formula and original source authority. Distinguish an
unfinished formalization/registration from semantic ambiguity. No further
source owner may be opened automatically.

## Already admitted direct inputs

Authenticate each hash before content reads. Only read sections directly
needed for the selected witness and formation-to-admission connection:

- `tasks/agent-loop/sprints/simple-sub-inference-soundness-r184-v4.md` —
  `518ee36cf16c5266a9cd7aabfec25eb7e42ceba9c9e6f7e9ce5970873d07b640`
- `tasks/agent-loop/sprints/yulang-canonical-inference-model-r187.md` —
  `999213b617db69cc2511692b6338f4c814fe8768d119ba477749124ee07b6218`
- `notes/theory/2026-11-02-yulang-canonical-inference-model-r187.md` —
  `da0f7aa365db0d3a97b6ba9988850c786e88eb9ffa6349eddfe964d25d7fd7c1`
- `tasks/agent-loop/history/complete-app-soundness-r188-outcome.md` —
  `312ca654be93d2f77a01bcc570f350cbf5b5db24d72305f1f2412291fc19a95b`
- `notes/theory/lean/YulangClosure/Contracts.lean` —
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` —
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` —
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md` —
  `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`
- `notes/design/2026-10-08-native-signature-formation-definition.md` —
  `e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9`
- `notes/theory/2026-10-08-source-signature-incidence-construction.md` —
  `7367ce8eb69376583386c6d675d067712ec6fa173e96f458ee34ce390dc8901a`
- `notes/design/2026-10-08-source-generalize-definition.md` —
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`

These are already authenticated mathematical owners from R184/R187; this
packet authorizes no new owners and no linked proof-producer body intake.

## Required outcome and parent metric

Return exactly one:

1. **SELECTED_WITNESS_ADMITTED** — construct the actual assignment-selected
   witness, its independent raw denotation/readout and the original admission
   derivation, then apply it to the outer `Judgment.existsE` in the original
   App source case. This discharges only that App sub-obligation; the rest of
   App and `InferenceSoundness` remain open.
2. **BLOCKED_AT_EXACT_FORMATION_EQUATION** — state the first actual generation
   or satisfaction clause needed, its exact type, the original owner/locator,
   and why the already pinned meaning does not derive selected-witness
   admission. Count zero sub-obligations discharged.

A universal all-elements admission assumption, renamed abstract domain,
selected witness chosen independently of `a`, or extra premise is not success.
Report the exact constructor sub-obligation discharged; do not use theorem
counts.

## Outputs and limits

- `notes/theory/2026-11-02-viewlogic-selected-witness-r189.md`
- `tasks/agent-loop/inbox/viewlogic-selected-witness-r189-proof.md`
- One fresh constructive `prover`: 1800 seconds.
- One fresh independent `spec_auditor`: 600 seconds.
- Total grant: 2400 seconds; no renewal, no parallel writer, no new owner.
- No Lean/Lake/checker, build, test, Rust, Cargo, environment, cache or scratch.

Review checks the original source constructor, assignment/telescope identity,
actual generated formation meaning, whether admission is derived for the
selected witness, and exact sub-obligation accounting. A reviewer cannot
promote a universal premise or a conditional wrapper.
