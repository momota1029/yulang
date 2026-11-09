# Cycle38: structural atom decomposition

Partial goal: expose payload-variable constraints from pair/arrow/equal-tag variant subtype atoms, with exact preservation of every assignment model, then feed the resulting atoms into verified contradiction pruning.

Data: actual PresenceNormalForm.Atom and TyTerm, finite lists. Independent judgment: Common.Subtype of eval values and All of original atom lists. Executable decomposition recursively replaces supported same-head type atoms with component type and row atoms. Other atoms remain unchanged. Structural size supplies recursion termination.

Target: for every variable type α, assignment ρ and atom list xs, All Common.model ρ (decompose xs) iff All Common.model ρ xs. For every list of states, contradiction pruning after decomposition preserves its entire model family. No satisfiability completeness or language classification follows from a negative conflict check.

Source: spec/04-types.md structural variance and existing Common.common_pair_iff/common_arrow_iff/common_variant_iff. No new semantics chosen. Latest Yulang2 audit fetch and new execution are not performed in this cycle; prior acquired audit material does not decide this structural core theorem.

General B4 still requires five bridges; this is within its constraint/model and diagnostic preparation, not completion of a whole bridge.

Extension of the same goal: before decomposition, derive endpoint constraints l≤r from actual lower l≤i and upper j≤r atoms linked by the existing finite directed reach closure. Add these entailed constraints, then decompose. This exposes payload variables even when the structured types are separated by ordinary slots. Exactness is for arbitrary assignments and the existing independent directed Path semantics, not guessed type equality. No repeated alternating saturation is claimed.
