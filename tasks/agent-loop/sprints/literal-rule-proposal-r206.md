# R206 — concrete source literal rule proposal

Status: ACTIVE under the user's standing goal and R205 end-dispatch selection.
Branch / baseline commit: `yulang3` / `072058f6d`.
Authority: user-approved static inference principles, R203 reviewed value/type introduction candidate, selected Source-Generalize §§3.1–3.2 and L1/L2. This packet proposes and compares a source rule; it does not adopt changed semantics.

## Objective

Sequentially revise only `notes/theory/2026-11-01-abstract-inference-model-r199.md`. Produce one concrete mathematical literal rule proposal that states:

- descriptor/type and value equations for every original raw literal constructor without changing payload;
- original Return at the same occurrence/event/world;
- intrinsic performed effects, while retaining contextual permission, inflow, residual and enclosing Call/effect obligations;
- admissible checking alternatives using the selected independent checking grammar, without erasing any original conservative alternative or guard;
- the original scope and one shared witness.

Compare the proposal against the selected SG literal rule and R203's explicit boundary. Either derive that the proposal instantiates already selected rules, or identify the exact additional semantic commitment. A difference requires a concrete accepted-typing/effect example or an exact rule/alternative that changes. Do not infer a user decision from missing equations alone.

The proposal must not be an opaque `LiteralMeaningΣ`/successful-check predicate, an assumed source judgment, a wrapper implication, or merely the list of required fields. Reuse the R203 raw-payload mapping as a candidate. Include all original literal constructors; do not narrow the source domain.

## Parent metric and gate

Unchanged root: `YulangClosure.SourceProblem.InferenceSoundness` (`Contracts.lean:128–130`) with the original quantifiers and one `sameScoped` witness. Parent delta is `0/4 roots; 0/5 packages`. A proposed source rule and its review are not parent-premise reduction. Do not attempt solver reflection until the source relation is fixed and actual generator/solution/readout equations are available.

If the selected authorities do not determine an alternative/guard or descriptor/value/root law, state that exact unresolved part and its two concrete completions; do not claim completeness or adopt one. If the proposed rule changes accepted source meanings, preserve it as unadopted pending explicit user approval under `rules/design-authority.md`.

## Frozen inputs and method

- R205 model candidate SHA-256 `ba39a6f187c9c483ebbff06b74e7484526f2a208fdacb23a2f1ab08f28c0534c`.
- R203 literal introduction SHA-256 `99af6a50a9b1a049000a834bcb6066ea3eb9fd51a17b84f8331797ffb9bd358d`.
- Selected Source-Generalize construction SHA-256 `e8ba493415b5fe1001086455d39ba47f543af66cb2cf65fcb8ebad939d4b2240`.
- `Contracts.lean` SHA-256 `2fc7186f47a4e1bf7af1fec3cd546b06394dbd3d8cec0660751554ce9f2bd72e`.

Primary construction only, then one fresh read-only review of the exact final candidate. No Rust reads/edits, Lean/Lake/build/tests, new files/storage, new environments/caches/targets/scratch/worktrees, or pending-question/quarantine access. Preserve R204/R205 and all unrelated worktree changes.

Budget: primary construction up to 600 seconds; one review up to 300 seconds. End with the exact rule status and original parent delta, then consult the dispatcher.
