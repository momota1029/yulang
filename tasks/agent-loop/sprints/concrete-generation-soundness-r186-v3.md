# R186 revision 3 — concrete generation soundness

Status: **ACTIVE bounded mathematical construction**, superseding revisions 1–2
only for the authenticated dependency set; the exact goal, proof grant and output
leases remain fixed. Baseline:
`yulang3` at `513af1ce8664581bd76480674e8275fb0bad1a7a`. User goal: establish
Yulang's type/effect inference guarantee against the original source rules;
Rust program correctness is outside this packet.

## Fixed parent and outcome

The unchanged parent is
`YulangClosure.SourceProblem.InferenceSoundness`,
`notes/theory/lean/YulangClosure/Contracts.lean:128–130`:

```lean
∀ s x d a, p.supported s → p.generates s x d → p.solves d a →
  ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a
```

Construct a concrete mathematical instance of the full generation-to-source
implication. Keep the original supported source domain, every solving
assignment, the same source scope, and one shared witness. The generator,
type/effect denotation, and source judgment must be independently defined from
the accepted source rules. Give actual constructor equations and apply the
result to the parent; a proposition interface, a list of remaining atoms, or
definitions without the all-constructor implication are not success.

Use syntax-directed constraint generation and induction on that generation.
The induction invariant must preserve the complete telescope, binder extension,
effect context and the same assignment. Cover the accepted expression, pattern
and statement constructors, including App/Call and contextual effects wherever
the governing rules use them. Use a concrete Function interpretation and its
four-port variance in the App case. Do not assume admission, source typing,
`Build` satisfaction, the desired witness, or unproved `LocalLaws`; do not
define `solves` to mean source typing/admission.

The mathematical theorem may be reported only when its exact parent application
is shown. Otherwise return the first exact constructor equation that resists
construction, the attempted independent definitions, and a mathematical
obstruction or counterexample. Missing existing Lean code alone is a formalized
construction gap, not semantic underdetermination or a reason to ask the user
to choose new semantics.

## Parent-premise ledger

| Named obligation | Before revision 2 | Required evidence |
| --- | --- | --- |
| Actual generation represented by one canonical constraint object | Unestablished | Concrete equations for all supported source constructors |
| Solving implies original constructor premises under the same assignment | OPEN | Induction case for every constructor, including effects and Call |
| Binder extension preserves scope and the shared assignment | OPEN | One explicit induction invariant and proved transport |
| Complete original source derivation follows | OPEN | Apply the complete theorem to `InferenceSoundness` |
| `PrincipalCoverage` and `InferenceTermination` | OPEN, separate | No closure claim in this packet |
| Rust/native correspondence | Later, separate | No Rust correctness claim or work in this packet |

Progress is measured by these named parent obligations removed or refuted, not
by the number of declarations or local lemmas.

## Construction method and falsifier

1. Define the finite supported source grammar and a canonical constraint object
   for every constructor, with an independently defined value/effect
   interpretation and source judgment.
2. State generation equations and the scoped substitution/binder invariant.
3. Prove the all-constructor generation-soundness implication. Apply each case
   immediately; App uses the concrete same-provider Function interpretation,
   not an independently selected port witness.
4. Apply it to the unchanged parent, or freeze the exact first unresolved case.

Falsify with a supported source constructor and generated constraint whose
satisfying assignment violates one original source premise under that same
scope, or with a concrete incompatibility among the pinned accepted rules.
An omitted constructor, stronger premise, changed quantifier, independently
chosen witness, or source-typing definition of satisfaction fails the packet.

## Exact assignment, outputs and resources

One registered `lean_prover` owns only:

- `notes/theory/lean/YulangClosure/ConcreteGenerationSoundnessR186V2.lean`
- `tasks/agent-loop/inbox/concrete-generation-soundness-r186-v2-proof.md`

One fresh independent `compiler_referee` review is reserved for the frozen
artifact, at most 600 seconds. Review checks actual constructor equations,
complete source coverage, independence/non-circularity, the scope invariant,
same-assignment application to the parent, theorem types, and full axiom audit.
The author cannot review their result.

Budget accounting: revision 1's 1800-second proof grant is fully charged
(elapsed/remaining UNKNOWN); revision 2 proof grant is at most 1800 seconds and
fresh review at most 600 seconds. Total authorized/charged envelope after these
grants is 4200 seconds, below the 7200-second sprint ceiling. No grant resets;
unused or UNKNOWN time is not returned. No Astra, Rust, Cargo, build, tests,
new environment/cache, root import edit, or generated scratch output. Use only
the existing pinned Lean project/cache if a concrete theorem is produced, with
one verification owner and at most two focused checker invocations.

## Authenticated inputs

Revision 3 adds three exact original source-rule owners required for the
independent generation/satisfaction construction. Their bytes were authenticated
by the primary before any content read:

- `notes/design/2026-10-08-source-generalize-definition.md` —
  `46884ce3717e4f7ae081e19581cff50bdbbf666941096f253df307d710d42a38`
- `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` —
  `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`
- `docs/yulang-source-type-safety-ja.tex` —
  `2c77bbd6f2679ac91ece3bb670152a9dfd16e033aa68545bff6c6dc509d24166`

No other authority or output path is added. The existing v2 proof grant and
exact leases continue without reset.

R186 revision 1's source/design inventory is inherited. Its malformed syntax
pin is corrected here; the actual digest was checked with `sha256sum`:

- `notes/theory/lean/YulangClosure/Contracts.lean` —
  `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`
- `notes/theory/lean/YulangClosure/SimpleSubConstraintSyntax.lean` —
  `a9ec574d31223e0484fd827838b45cd019fc858eece9f326c95ebc2e1e77a1f6`
- `notes/theory/lean/YulangClosure/OriginalSourceSyntax.lean` —
  `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1`
- `notes/theory/lean/YulangClosure/OriginalSourceGeneration.lean` —
  `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef`
- `notes/theory/lean/YulangClosure/OriginalSourceEnvironment.lean` —
  `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132`
- `notes/theory/lean/YulangClosure/OriginalSourceInterpretation.lean` —
  `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef`
- `notes/theory/lean/YulangClosure/OriginalSourceChecking.lean` —
  `a0ba215e28fe0152e3c66024da86ab9a63219b7950e741bf260cbc4c2897ffd6`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md` —
  `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`
- `notes/design/2026-10-08-contextual-function-membership-definition.md` —
  `0341e44bcc01b916ca5b2cd1c7e95622d8dd3b562a7c2480d2e0241542e1f5d0`
- `notes/theory/2026-10-08-call-semantic-input-realization.md` —
  `fd781ba2d76b239724b86183985c612fe3bbd3542ff8d47860705c9c3752226a`
- R185 proof inventory —
  `tasks/agent-loop/inbox/yulang-generation-soundness-model-r185-proof.md`,
  `0f869c9973939788fd73ac4a251ebb6eec18800e4972d67cb6b5dd1a44016eda`
- R186 revision 1 stop receipt —
  `tasks/agent-loop/inbox/contextual-function-interpretation-r186-proof.md`,
  `a83c74cd4f7f4d8347b5d02c5acc4946134d8904838197446d09481fd8da9bec`

Also inherit the remaining exact source/design/approved-answer pins from R186
revision 1 without alteration. Authenticate every pin before reading its
contents. Any additional direct declaration owner required by the actual
construction must be identified and pinned before its contents are read; no
Rust/source-code census or broad solver-import survey is authorized.

## Stop and handoff

Stop at the grant, a changed pinned input, missing semantic authority, a
required scope/meaning change, an actual counterexample, or the first exact
constructor gap that cannot be resolved from accepted rules. Preserve failed
attempts and distinguish constructed, kernel-checked, reviewed and parent-
applied results. Report full theorem types and complete `#print axioms` output
for any checked theorem. Record exact writes, checks, budget and stopped-writes
receipt in the one leased handoff. Principality, termination, source/native
correspondence and Rust remain separate gates.
