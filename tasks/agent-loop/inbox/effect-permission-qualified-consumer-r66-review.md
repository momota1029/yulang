# R66 independent review

Verdict: **PASS for the bounded R66 research contract**, with no BLOCKING, major or minor findings. This does not certify Rust compilation, native execution, source/native correspondence or the original A/B obligations.

Authenticated frozen bytes:

- Contract: `e3bad12e18f09bc01992c68f0f1f5c02bdcb5f6c7ed4b508cd814a5c2409fd38`
- Rust: `253c0e469b91a30580a65ec57569a20ed7ad53fd7d7e82c0dc7d2e71102fad1a`
- Lean: `5db5ad3f3f5e5803e2bc564fc8922d5eb8a72182c7ba11de3904eebd7b5950e1`
- Rust handoff: `540f0ed4d616824f53860aa5b460a26953c129f0d409324e14361c39af0db787`
- Proof handoff: `2d8c38878553713b475e32c6846be8a1c05a6b63d3345db1a851eb6660112039`

All pinned R65/R62/R60/R61/R49 inputs match. Initial substantive inspection used code, definitions, governing annotation policy and tests before reading author explanations.

The change addresses the downstream ownership cause: R66 computes source incidence and selected root using R65 readers, then constructs the R49 Context from those same objects. It does not merely prove another disconnected lookup result.

Reviewed seams:

- `candidate_receiver.rs:745–854`: the private borrowed view joins the selected source call, schema owners, DefinitionUse, occurrence-qualified slot 0/2 records, route, registration, recipe, permission coordinates, raw entry and indexed emission/admission. `:3383` requires that view during private package capture. Fact selection counts every competitor at the source key before testing selected fact identity; distinct-key shared identities remain possible.
- `OccurrenceQualifiedConsumerR66.lean:99`: root selection retains R62’s emission/admission/readback/relation checks and qualified R47 source/cause/task/completion checks before ancestry.
- `:212`, `:318`: successful first-entry policy supplies the R45 certificate and R47 Matches for the constructed consumer Context. Ancestry remains checked through the actual R61 callback.
- `:259–315`, `:361`: Context uses the identical R65 inventory/current, request use, selected fact, full permission, raw entry and root relation. The ten remaining consumer premises are explicit; authentication is derived from them.
- `:456–495`: physical decoder agreement is proved, and successful outer Run, Checked and terminal equality remain independent premises.
- `:412`, `:503`, `:516`: finite evidence reaches policy and publication with a shared FactId at distinct occurrences; preserves ordered duplicate contributions under known-unmatched forwarding; rejects duplicate route/lambda keys, foreign store, substituted source root and injected Context root.
- `:541`: collected Catch slot 51 retains the original reader.

I inspected the four existing receiving-residual tests without running them. Their matching/unmatched, grouped scrutinee and private-envelope boundaries remain unchanged.

Verification evidence was authenticated without checker reruns. Both final compressed stdin inputs match their recorded hashes; their 13 namespace sections retain source lines in original order from the current frozen files. Generic input contains all 17 generic R66 theorem declarations; finite input contains all three finite roots. The retained receipts report Lean 4.35.0 exit 0 for both groups and complete types/axiom audits for all 20 roots. Only `propext` and `Quot.sound` occur. No holes, project axioms or checker bypasses appear in those inputs.

Remaining limits are correctly OPEN: actual package interpretation into Lean, pointer/token/index authenticity, complete native provenance/path/provider inventories, actual resource outcomes and successful outer executions. Rust was reviewed statically only. I made no writes, builds, tests, checker runs, scratch/cache/worktree creation or author contacts. Review complete; writes stopped.
