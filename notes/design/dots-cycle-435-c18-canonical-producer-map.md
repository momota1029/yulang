# C435 / C18: the prior native producer is an exact canonical R17 source

Source-level proof plan against `ef109ee6e6150ea80513ee4bcef8a081d88899a1`. This addresses whether the genuine C405 producer used by C406 is also a source derivation in the current system. It does **not** put the completed-lower consumer into the fixed system and is not a newly compiled Lean theorem.

1. `PriorSource406` is exactly `authoredNativeSelectedSource405`. `FixedEvidenceFamily407.authoredNative` injects this prior rule into R0, for both `elected` and `other`, at the same event and dependency list. The existing C407 local proof is a disjunction of rules per node, not a disjunction over entire programs.
2. For each current named-rule step, there are two arrows of type `NamedRuleMap428`: for selected and for other rules, with all State, Request, Event and support-list indices unchanged. Each arrow is either definitionally identity (=) or the left injection into the actual local rule union (+), as read from the pinned production definitions:

| From | To | elected / other |
|---|---|---|
| `R0` | `Named409.R1` | `+ / =` |
| `Named409.R1` | `List410.R2` | `+ / =` |
| `List410.R2` | `WhereCycle411.R3` | `+ / =` |
| `WhereCycle411.R3` | `RecordK2412.R4` | `= / +` |
| `RecordK2412.R4` | `MixedRecord413.R5` | `= / +` |
| `MixedRecord413.R5` | `OpenTail414.R6` | `= / +` |
| `OpenTail414.R6` | `ClosedResidual415.R7` | `+ / =` |
| `ClosedResidual415.R7` | `PlainMerged416.R8` | `+ / =` |
| `PlainMerged416.R8` | `X6Ambiguous417.R9` | `= / +` |
| `X6Ambiguous417.R9` | `RigidRival418.R10` | `+ / =` |
| `RigidRival418.R10` | `ExplicitPick419.R11` | `+ / =` |
| `ExplicitPick419.R11` | `RoleDefault420.R12` | `+ / =` |
| `RoleDefault420.R12` | `RepeatedCenters421.R13` | `+ / +` |
| `RepeatedCenters421.R13` | `EndpointProjection426.R14.named426` | `= / =` |
| `EndpointProjection426.R14.named426` | `StructuralWhere431.R15.named426` | `+ / +` |
| `StructuralWhere431.R15.named426` | `WhereAssociated432.R16.named426` | `+ / +` |
| `WhereAssociated432.R16.named426` | `PendingAssociated434.R17.named426` | `+ / +` |

Source anchors: R0 blob `8af8804db399afe2753bfdb68c55b22b460e6b1f`; R1 `7c9de0e0718d0cd71e66fef33f737b57b465aabd`; R2 `120cd30c3378b1b7d4361fd1fc2cdfd2a3302591`; R14 `750abcee0904c47e48e04845f5e46ec9c2ef3728` (the named view is definitionally R13); R15 `e3d303c9f830b10fd4b6f08d26d936980456c475`; R17 source `5cb47c895106cdd316b035e53d26877b354e2527`. Intermediate proofs follow the directly read published R3–R13 rule definitions, not a checker success implication.

3. Compose these local maps, then take one structural fold on the actual old `SourceTrace PriorSource406 s producer t (some e)`. `mapNamedTrace428` (StructuralWhereEmbed428 blob `95c19bdd007c2efc638e42787d8744b197a15cee`) already expresses the desired proof: it outputs a replay indexed by the same `s`, `producer`, diagnostic tree `t` and exact original event `e`, preserving ordered writes and needs. Its support operation keeps each existing `sameTypedOutput` equality, not a re-found producer. Original root K2 is unchanged.
4. That same summary `Summarizes t (.selected d)` and the lifted trace give a canonical `Classifies R17 s producer (.selected d)` by named-lane inclusion. Exact producer output number, typed receipt and target used by the completed dependency therefore need not be weakened to just an equal name or model value.

The structural mapping function is currently declared noncomputable (its result also proves equality of the existing noncomputable report encodings). Do **not** use it as the runtime producer constructor. Build the original PriorSource406 proof in Type from the actual reads, as in the neighboring replay note. The map above is a separate semantic audit of that actual producer; if a computable lift is later needed, factor a pure mutual recursor rebuilding the three source/where/support constructors, keeping the equality-of-encodings proof separate. Do not run an old checker or a classical choice to manufacture provenance.

For C18 itself only the old producer is embedded. The new consumer still needs a separate completed-lower judgment, and the no-authorized-lower proof blocks its admission into the old fixed carrier. This split would let a future scoped executable witness contribute evidence for a genuine older canonical producer without implying C18 is already implemented.
