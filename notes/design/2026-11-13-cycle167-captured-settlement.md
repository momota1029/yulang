# Cycle 167: captured settlement boundary

## Question and scope

After the actual producer installation and actual scalar refresh of cycle 166,
can a Trusted explanation reuse the parent output to obtain the captured alias?
The full journal already entails the scalar consequence. That semantic fact is
not by itself a Trusted explanation.

## Construction

Use only existing `Alias`, `Discharged`, and `Trusted` constructors. With no
alias edges, a discharged occurrence must have the identity of some recorded
packet. The actual observed journal contains only the producer candidate and
the parent packet; neither has the consumer identity. Therefore the consumer
is not discharged. Separately, induction on a Trusted derivation proves that
every output fact in its slice comes from a settled packet. The parent packet
requires the consumer to be discharged, so its output cannot appear in any
Trusted slice of this actual observed state.

The first three lemmas quantify over arbitrary role declarations and states.
The final two specialize to the existing captured-input fixture. No execution
rule, guard, observation, schema, or semantics is changed.

## Verification and boundary

New module: `GeneralDictionaryCapturedSettlementBoundary`.
Focused Lean compilation and `Audit/Cycle167CapturedSettlement.lean` pass with
`--trust=0`; dependencies are only propext, Classical.choice, and Quot.sound.
No sorry, added axiom, native_decide, or full repository build is used.

This is NOT a proof that `ReadyAt observed 2` is impossible. It excludes the
specific parent-output alias route in `GeneralDictionaryCapturedTrustedBoundary`.
An independent trusted alias explanation, or a genuine all-slices countermodel,
remains needed to resolve the stronger question. General V5 is not closed.
