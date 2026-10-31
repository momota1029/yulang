# R75 outcome — distinct source-root and emission relations

Sprint: `EFFECT-PERMISSION-SOURCE-ROOT/20261031-R75`  
Disposition: **CLOSED_BOUNDED_SOURCE_REPAIR_AND_CONDITIONAL_LEAN_ACCEPTED**.  
Parent objective: unchanged `research/simple-sub-intrusion` / Yulang soundness.

## Result

The private Internal-root inventory had conflated two relation roles. Its
source-use root is selected from a Value pair, while the entry emission's
admission relation is authenticated against a fresh Effect bound. The old
inventory guard required the admission relation to equal the source root
relation. Since the relation reader is functional and the Value/Effect pair
constructors are disjoint, that guard rejects the checked mixed case before
the inventory view can be returned. The existing native ancestry check already
connects the emission descendant to the source-root ancestor.

The Rust repair retains `source_root_relation`, its checked source Value pair,
and `emission_relation` separately through request validation and the returned
private view. Each ID is checked against its own indexed table row and typed
pair. It removes the cross-role equality while preserving the existing
physical-slot, source-use, identity, admission/emission, bound and ancestry
checks. The helper and ordinary inference behavior were not changed. The path
is feature gated and has no ordinary inference caller identified; this repairs
private evidence construction and is not a demonstrated runtime change.

The Lean module imports R47's actual `Endpoint`, `Inputs.relationPair`,
`Query`, `Probe`, `Matches`, and ancestry definitions. It proves functional
typed Value-root and Effect-emission rows have different IDs, derives
rejection of the old guard, preserves the R47 root-to-emission ancestry and
remaining ownership conjuncts, and constructs a finite R47 fixture accepted
by `extract` but rejected by the old guard.

The result does **not** construct an actual R66 `Root`, authenticate a Rust
package's extraction into the finite model, establish a native source run, or
close original A/B or production.

## Proof execution and deviations

The first direct Lean stdin audit exited 1 after 6.625 seconds. Six general
theorems checked with `propext`/`Quot.sound`, but fixture proof synthesis failed
and Lean recovery introduced `sorryAx` in the failed declarations. Those
declarations were rejected and repaired. R39 had been measured before that
first execution but was missing from the primary's original input manifest;
this prior-pin deviation is preserved in amendment 01 and the proof handoff.
The amendment did not retroactively authorize the first run.

After amendment 01 was committed, one exact repair audit ran on the frozen
64,305-byte flattened stdin (`8b3b30ed3a8333573aa5a78b923819491be56456f7d0e958085a4f0ec119d91c`)
with the pinned Lean 4.35.0 executable, `-j1 -M1024 --stdin`, and a 120-second
timeout. It exited 0 in 6.718 seconds and produced 13 theorem type/axiom
reports. Transitive axioms are `propext` for
`value_effect_disjoint`, `typed_relation_ids_distinct`, and
`mixed_local_ownership`; the other ten use `propext` and `Quot.sound`. No
`sorryAx`, `Classical.choice`, project axiom, or checker bypass occurs in the
successful artifact. The successful stdout SHA-256 is
`b1053c85ddf239c336f80964a5088533d80814db116592c7b0253b90353e029d`; stderr
was empty. No `.olean`, `.ilean`, cache, or other generated file was emitted.

The independent reviewer reconstructed the successful stdin and stdout in
memory, matched both hashes and all 13 declarations, and accepted the bounded
result with 0 blocking, 0 major, and 0 minor findings. Review did not rerun
Lean.

## Evidence, checks and Git

- Contract R1 SHA-256: `bbeb3cc4bf26a8fe29b2144dc086e6e0efa6bd7c0f9d2ec5ab8aeab8401db3fb`.
- Input manifest R2 SHA-256: `518ff1313ecc5c837c5fd97bd958ad879ddf585b18e3783c915b695cef916db6`.
- Amendment 01 SHA-256: `9f3ecd46bcb2cef58783f8f525502f152310ce8c1df219dbc2f1bac8ba44fd6d`.
- Rust source SHA-256: `29fccb4808106f13e761f97c9bda1201f175944dccb916e437edaf1b694609fd`.
- Lean module SHA-256: `e868eb6bc6cba74af4f3096cc7fb2e48503c8183e064071b84022923c2bc6821`.
- Rust handoff SHA-256: `eba8078634d385151a8914e3d640be541ef8f1930e57ddbc0095e2acd649290f`.
- Proof handoff SHA-256: `2fa485cec5db25e428941536bf2bc78982ae0e2dbda9adc9a5cd1fa433033bee`.
- Review report SHA-256: `a1c36e691f09c0c28242fa3b5261263673be577497a887e438232f00d1e3dae0`.

`git diff --check` passed on the frozen paths and `python3 tools/agent_sprint.py
check` passed after worker/review state updates. These static checks are not
Rust compilation or integration evidence. No tests, Cargo, compiler, build,
formatter, Lake, extra environment, worktree, cache, target or scratch path was
used or created. Rust type checking/runtime and project import integration
remain **UNVERIFIED**.

Reviewed implementation checkpoint: `f3cabaec1` (`fix R75 distinct source
and emission relations`), pushed to `origin/yulang3`. Earlier R75 admission,
author-launch, amendment, and reviewer-launch checkpoints are also pushed:
`f0217b942`, `ed14939a8`, `b1f40e6f8`, `9fa5f7628`.

## Remaining type-theory and source obligations

The earliest source premise still missing for genuine R66 construction is the
unique plan for the exact Internal use, together with successful
`ownerSelection` at the planned target-root component and its parameter
recipe. R45 `OwnerReads` does not establish that global selection. R73
`OwnerDecoded` contains no R55 formal/permission/receipt/plan/recipe inventories
or R57 emission/admission/Origin inventories. Independently authenticated
same-artifact incidence, current-slot readbacks, unique source-drain root,
physical identity and native ownership must still derive every `Root` field;
assuming `Root`, successful `readRoot`, or successful policy is not a
construction proof.

Therefore actual source/native extraction, genuine R66 `Root`, original A/B,
whole-language soundness and production remain **OPEN**. No semantic gate or
claim was weakened.

At the sprint boundary, `next_action_selector` recommends R76: construct the
same-use plan and R66 global formal-owner selection from complete source
inventories, then derive the exact parameter-recipe equation. Supplied plan,
selection result, `Root`, or `readRoot` success cannot serve as the constructor's
premise. The selector's proposed attacks are duplicate same-use plans, multiple
eligible origins, missing/duplicate recipes, a wrong target-root component,
wrong parameter index, and a shared Function/row with a foreign registration.
