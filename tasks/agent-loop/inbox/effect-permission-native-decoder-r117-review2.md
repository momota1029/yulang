# R117 revision 2 independent static review

Verdict: **ACCEPT as an unapplied, uncompiled research patch candidate only.** No BLOCKING, major, or minor compiler-correctness finding established within this packet. This does not authorize source integration or close a proof/production gate.

## Frozen identity and method

Independently calculated SHA-256:

- Patch: `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`.
- Rust handoff: `6557b368fb1f092d5c4151cb54d74c7dd61c92153105e8720b17189c1efd128e`.
- Proof map: `0d5d17927a9b1cd2c7c72fb8b1ba0f7be44c146f7057cd1730b1b31dfcd32e53`.
- Pinned `candidate_receiver.rs`: `6004fd4252d15d8c99ac0e9f97582347a0de94946f497c0e29520d872e77dae2`.
- Pinned `candidate_effect.rs`: `1c80c55c62b724b9d2080bd2ddcdabfa35a5ba641c1bf45d9735dfd7fd05be41`.
- Pinned `candidate_source.rs`: `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`.
- Pinned `lib.rs`: `c43fcc4f39e4ba8bfea10aa39879c37973100d9f4b8bdef71fa5b3dc3fae01df`.

Read the frozen sprint contract, patch, exact pinned Rust blobs using read-only exact-path `git show`, relevant baseline owner/construction/consumer branches and receiver tests, then the handoff/proof map. Initial conclusions came from patch and baseline rather than the implementer explanation. Hashes authenticate bytes, not semantic claims.

## Independent checks

All six hunk body counts agree with headers: old/new `4/8`, `7/11`, `12/32`, `3/7`, `4/10`, `12/43`. First five old contexts match their stated pinned offsets. The final hunk old context begins at baseline line **5109**, three lines after its advertised `5106`; its corresponding new context begins at 5147 rather than 5144. Its complete old context is present and contiguous. This is an offset in valid unified-diff metadata, not a demonstrated application failure; no application was attempted.

The change repairs the missing authentication at its existing observation owner: provider capture joins the actual retained permission to the selected native member, and existing package assembly consumes that join. It does not attempt to repair suppression by filtering a downstream result.

- **Payload pointer level:** patch hunk at baseline 1860 matches `&(usize, &FormalEntryPermission)` from `self.permissions.iter()`. Therefore `permission` is `&&FormalEntryPermission`; `std::ptr::eq(*permission, self.catch.permission)` compares the actual retained payload addresses. It no longer compares a vector element reference slot against the payload address.
- **Registration versus storage position:** both patched searches filter on the record field `permission.registration`, require exactly one match, and carry the separate tuple position as `permission_index`. Baseline `candidate_effect.rs:387–390` enumerates the compact retained vector; `:1785–1821` retains a record only for nonempty concrete annotations. Thus registration 0 with no record followed by registration 1 produces `(0, record(registration=1))`: capture finds the record by 1 and carries 0; the package finds it by 1 and compares its carried storage position to 0. Baseline `candidate_receiver.rs:1871` still indexes the separate complete formal-registration table by 1, which is the correct namespace.
- **Different registration/state:** duplicate or missing registration is unavailable; source formal, parameter, occurrence, owner, scope, annotation/row keys, entry ordinal and concrete allocation identity are checked against Internal incidence. Owner/batch/live-context pointer checks precede composition (new hunk at 5052); baseline source inventories also round-trip against the owner (`4338` onward). Foreign state or equal-looking foreign records cannot satisfy the checked pointer chain.
- **Same spelling, distinct operation:** full provider/selected-arm/declaration operation IDs are compared in the final hunk. Baseline capture also requires the actual operation-origin declaration Arc and occurrence (`5098–5110`), and source round-trip checks the actual selected Catch arm declaration (`4521–4530`). Equal spelling or family alone does not authenticate another operation.
- **Wrong endpoint or missing provenance:** baseline `5092–5107` requires an AnnotationMember, exact owner view pointer/index, closed tail, selected allowed member and operation provenance. Added fields preserve the member and family; package consumption checks the typed endpoint, view/member coordinates and the owner allowed-family read against retained permission membership. Row/member/family integer namespaces are never identified by numeric coincidence.
- **Fact namespace collisions:** baseline `ProviderFactOwner` distinguishes BatchOccurrence from SemanticStore (`219–221`); package capture rejects SemanticStore (`4822–4826`) before fetching the collected fact and checking pointer/occurrence/slot. No patch hunk erases that tag.
- **Consumed assembly:** baseline package capture calls provider capture (`4614`), carries the new fields into InventoryCatchRequest (hunk 4844), and calls `package.internal_root_view()?` before returning (`5036`). The newly checked receipt is on this mandatory successful observation path, not a disconnected accessor.
- **Failure isolation and restoration:** added branches return only optional projection `None`/CurrentEmissionGap. They perform borrowed reads and local inventory work; no solver state or rollback journal is mutated. Existing ordinary execute/suppress paths are untouched. The candidate can make this matching-provider observation unavailable for unsupported cases without changing ordinary inference.

Read baseline tests at `candidate_receiver.rs:5704`, `5719`, `5748`, `5764`: exact matching signal, same-spelling different family, grouped scrutinee, and private-envelope rejection with ordinary candidate admission retained. They are relevant existing controls, not execution evidence for the new guards. No new or altered expected output appears in the patch.

## Evidence limits and residual ownership

No compiler, Cargo, build, test, Lean/Lake, checker, formatter, patch application, dirty Rust source read, scratch/cache/worktree/environment experiment, Git mutation, or descendant was used. A first invocation of unavailable `python` exited 127; static inspection used `python3` afterward. No generated artifact beyond this receipt was written. Rust type/borrow checking, actual patch application and executable rejection controls remain unestablished.

The proof map explicitly describes proposed symbols and does not claim independent inspection of the frozen patch. The independently checked Rust chain above supports those proposed field roles, but neither this receipt nor that map supplies a Rust-to-Lean interpretation. R116 kernel acceptance and complete axiom audits, R39/R45 successful-constructor equations, exact source/native decoding, R114 admission transport, original soundness/effect-hygiene quantifiers, principality, termination and production remain OPEN. The pinned Lean artifacts were not independently proof-audited in this static Rust packet.

## STOP receipt

Review packet R117 revision 2 complete. Sole owned output: this receipt. Writes STOPPED; no descendants, generated outputs, scratch paths, source edits or Git mutations. Frozen patch and input artifacts were not modified. Return to primary for adjudication and research-artifact checkpoint only.
