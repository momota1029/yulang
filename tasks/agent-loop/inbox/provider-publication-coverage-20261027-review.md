# Provider publication coverage — independent review r1

Sprint: `PROVIDER-PUBLICATION-COVERAGE-20261027/r1`.
Reviewer: `/root/provider_publication_review`, non-author; effective model/effort UNKNOWN.
Contract SHA-256: `e3996c31afb32756468068b25b587bcd7499cc0a4d628383b54780c490f8753d`.
Baseline supplied by contract: `b54ae2df5dd0113779ee95d380cfcbdbd2fb14e0`, `yulang3`; no Git authentication performed.
Method: actual proof/audit/trace/adapter and original definitions inspected before producer explanations. Then both frozen handoffs and preserved execution receipts were compared. Read/hash only except this exact leased review file. Applied `yulang-lean-proofs` for claim/scope/audit discipline; execution explicitly excluded by the review packet.

## Verdict

**Accept as reviewed conditional mathematical argument and authenticated Rust provenance evidence; INCOMPLETE as checked proof or source-qualified provider realization.** No mathematical error was found in the finite-support argument or compatible total-map construction under their written assumptions. No compiler semantic change is present in this packet. The missing proof acceptance and original source/semantic instance below prevent completion of the sprint's proof outcome. Every parent gate remains **OPEN**; no source-qualified Yulang counterexample is established.

The change addresses the cause of the earlier coverage obstruction: open execution is universal over the original admitted domain, which permits arbitrarily re-scoped occurrences, rather than merely the observed finite list. It does not repair or establish the absent source/semantic owner bridge.

## Findings and closure requirements

### F1 — BLOCKING for proof acceptance: no successful check or complete axiom audit

Locations: `OriginalProviderPublicationCoverage.lean:22,36,49,75,90,129,137,161,178,232,263,292`; `AuditOriginalProviderPublicationCoverage.lean:1–39`; preserved `proof/call-7.log` and `proof/call-8.json` under the sprint scratch root.

The last targeted build failed at line238 (`No goals to be solved`). The final source repairs that tactic sequence to `cbv <;> simp`, but no successful final module build exists. Call8 used the exact final module body with additional audit imports, then exited -9 after the per-process RSS monitor observed 1,074,954,240 bytes; its log is empty. The final import-only audit is a subsequent unexecuted artifact. Disappearing other diagnostics in a failed build cannot establish acceptance or exclude inherited `sorryAx`/unapproved dependencies. The trace also has no Lean acceptance receipt.

Invariant: sprint proof contract's final delivered-type/complete-axiom audit requirement and the skill's separation of constructed, checker-accepted, reviewed and source-corresponding evidence.

Minimum closure: a separately authorized verification owner must build these exact frozen proof bytes against the pinned dependencies, then obtain each actual fully qualified type and complete axiom dependency list, with no holes/bypasses or unapproved axioms. Do not rerun under this exhausted envelope or promote source signatures to checked types. The handoff honestly identifies this limitation; this is an evidence blocker, not a discovered false theorem.

### F2 — major for source/provider closure: conditional construction has no authenticated semantic instance

Locations: `OriginalProviderPublicationCoverage.lean:240–261,292–312`; `OriginalProviderPublicationCoverageTrace.lean:42–52`; adapter `original_provider_reify.rs:214–343`; `OriginalProviderSourceSolution.lean:14–37` (coordinate parameters, not owner certificate).

The provider conclusion is a constructed conditional theorem. Its `InitializerPremises`, outer Shared admissions and binding Local proofs are not supplied for the authenticated provider, and neither are its original Source coordinates/incoming Context, semantic Inputs/readout/admissions/Kernel/environment, open replay or compatible actual map. The negative theorem likewise has no authenticated admitted outer Return or finite-support premise. Therefore neither route proves a provider solution nor refutes the real provider. Changing only publications leaves admission unchanged, but original Kernel atoms/checking can depend on that map: initializer and Local premises are correctly required in the completed map, and cannot be silently transported from the old environment.

Invariant: parent theorem's original source scopes and independently established local laws (`2026-10-13-intrusion-source-preservation-proof.md:16–44`); selected Source-Generalize construction §§3.1–3.4 requires the same actual provider, complete tuple and independent source legality, rather than exporter/resolver success.

Minimum closure: the original source/semantic owners must supply `PSR-SOURCE-OWNER-1` first (authenticated Source/Site/Name/Declaration and genuine incoming Context), then the one coherent environment/admission/Return/Shared/map and local checking evidence needed at `PSR-EVENT-MAP-1`. The two Rust identity joins still need original publication-name equations at `PSR-EXPOSURE-TRANSPORT-1`; full import-root elaboration remains separate. No fake empty Context, successful Kernel, finite Return list or occurrence filter closes these obligations. This is an explicitly retained research boundary, not a regression introduced by this submission.

### F3 — minor receipt defect: stdout omits the declaration range end

Location: adapter `original_provider_reify.rs:346` prints only `range_tuple(&declaration_range).0`, producing `provider_declaration_bytes=0`. The source handoff's claim that the successful output identifies `(0,12)` needs the generated trace as well as stdout. A future reader relying on that receipt alone cannot authenticate the declaration end.

Invariant: exact source-range provenance and accurate evidence reporting. Minimum closure: describe `(0,12)` as a trace value authenticated by the adapter's range guards, or print the complete tuple in a later authorized adapter revision. This does not invalidate the current trace: its full range is emitted from the checked HIR range and independently joins the export range. No compiler correctness change is requested.

## Mathematical review and alternate paths

`Admitted` (`OriginalSourceEnvironment.lean:638–646`) checks the complete parent event path and decoded admission of the payload, with no occurrence test. Thus `rescope_admitted` preserves the actual payload and parent scope at every Nat occurrence. `executionOpen` (`OriginalSourceGeneration.lean:762–766`) quantifies over every such candidate. `provider_solution_requires_fixed_record` forces an exact record at each resulting key. Any finite-support key list has a strict bound given by `supportBound`; choosing that occurrence makes the required key's path sum at least the bound, contradicting membership. Existing records do not avoid this argument. Empty prior publications are needed only to show the old finite-list completion has finite support.

The quantifier boundaries matter: with no admitted Return, the universal outer branch may be vacuous; with fixed replay, the separate `executionFixed` constructor selects a history instead; with an infinite-support map, no finite bound follows. None of those cases is covered by the negative conclusion. The artifact does not assume them away for Rust. Repeated or colliding logical coordinates do not make different re-scoped occurrence numbers collide, since the Return event path retains the Nat occurrence.

`totalCompletion` covers every originally admitted Return, preserving every prior record. Original parent scoping plus key equality implies equality of the complete scoped candidate (`scoped_return_identity_injective`), so classical representative choice cannot select a different record at the same key. `Compatible` requires equality of the entire prior/candidate record, including entry/capture names, fixed Return/Shared frames and initializer snapshots. A prior record with even one different capture/frame at an admitted key makes compatibility false: no extension can both preserve that prior record and cover the candidate. This is the correct obstruction, rather than overwriting prior records or checking only identity. No finite-support claim is made for the total function.

The provider and initializer construction follows the actual generated rule tree: description/view existentials precede universal invocation; receipt precedes universal formal Return; Shared uses the same anchor; body EventProof and local computation checking remain under the event. Invocation extension resets replay, justifying the inner open execution without an extra global replay assumption. Outer initializer entry preserves replay, so `provider_from_total_completion` explicitly retains `openHistory`. Rule-forest siblings share the same environment; no initializer child state is improperly threaded into the outer binding sibling. Both outer binding atoms and the empty published suffix are present. None of this instantiates the local semantic premises.

## Rust correspondence and evidence boundary

Inspected actual owners: `parse_file` / parse-branded keys (`full_parse.rs:130–138,345–369`), ordinary-source `lower_module` (`module.rs:2182–2192`), owner-checked LocalSource/definition queries (`module.rs:2022–2043`), artifact-branded occurrence ownership (`module.rs:2103–2105`), named Lambda/formal/body construction (`local_source.rs`), complete source imports (`module.rs:800–810`) and full `SourceExportId` (`source_exports.rs:163–184`). Relevant existing tests were read, not run: `source_node_keys_preserve_clone_brand_and_reject_reused_green_root`, `ordinary_carrier_reuses_branded_roots_parameters_and_namespace`, and `source_imports_resolve_named_alias_and_glob_by_exact_provider`.

The adapter checks the exact public HIR binding, owned definition key, one definition-owned named group, Lambda formal identity, parameter-resolved body, source slices and parse ownership. Foreign parse and foreign HIR occurrence rejection execute before the sole trace write, followed by positive ownership of the selected provider body. `identity` and implicit prelude `id` are each compared against the complete provider export identity, including source key and syntax kind; displayed module/name/range rows alone are not used for equality. The fixture hash independently recomputes to `9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e`.

Preserved attempt2 stdout/stderr/time/status substantiate exit0, foreign-owner checks and both exposure joins. These are reviewed historical runtime receipts, not a fresh execution by this reviewer. The trace matches the adapter's constructor-owned values. Its booleans/ordinals do not retain transferable Rust brands and are not logical certificates. The consumer is resolved by the import API; no claim of executed consumer application follows. No original Source/Context, admission, actual initializer Return/Shared frame, replay or publication-map equation is constructed. The first owner gap is Source/Context introduction, before event/map realization.

The original whole-language soundness/principality/progress/termination and complete Call/effect hygiene obligations remain OPEN. The top-level principles §1.1 require applying established hygiene results at their actual constructor/consumer hypotheses; this packet neither restarts those results nor supplies their missing source/native bridge.

## Delivered declaration status

Namespace for every row: `YulangClosure.OriginalProviderPublicationCoverage`. Exact written signatures are at the indicated lines in the frozen proof module, with source-signature copies in the proof handoff. **Printed/elaborated type and complete axiom status are NOT_OBTAINED for all twelve declarations.** No axiom-free or standard-axiom-only claim follows from the source scan. The final audit names all twelve roots; the reviewer found no explicit proof holes/project axiom/checker bypass in the new module, which is not a transitive audit.

| Declaration | Source line | Printed type | Complete axioms |
| --- | ---: | --- | --- |
| `key_bound_lt_support` | 22 | NOT_OBTAINED | NOT_OBTAINED |
| `rescope_admitted` | 36 | NOT_OBTAINED | NOT_OBTAINED |
| `finite_support_no_open_provider` | 49 | NOT_OBTAINED | NOT_OBTAINED |
| `finite_completion_support` | 75 | NOT_OBTAINED | NOT_OBTAINED |
| `empty_prior_finite_completion_no_provider` | 90 | NOT_OBTAINED | NOT_OBTAINED |
| `total_completion_preserves_prior` | 129 | NOT_OBTAINED | NOT_OBTAINED |
| `total_completion_contains_admitted` | 137 | NOT_OBTAINED | NOT_OBTAINED |
| `compatible_iff_extension_exists` | 161 | NOT_OBTAINED | NOT_OBTAINED |
| `total_completion_publication_valid` | 178 | NOT_OBTAINED | NOT_OBTAINED |
| `initializer_source_rules` | 232 | NOT_OBTAINED | NOT_OBTAINED |
| `initializer_from_local_premises` | 263 | NOT_OBTAINED | NOT_OBTAINED |
| `provider_from_total_completion` | 292 | NOT_OBTAINED | NOT_OBTAINED |

## Frozen review snapshot

All hashes independently recomputed from actual bytes. Imported Lean pins and Rust owner pins match the contract/handoffs.

| Path | SHA-256 |
| --- | --- |
| `OriginalProviderPublicationCoverage.lean` | `62257d276004f6caf07872142e4a4369266d5205d992f4f3d56f36657ae69783` |
| `AuditOriginalProviderPublicationCoverage.lean` | `0efb9acdef8be952d59c7faccc0b8dff21ad8ec813a8417c0742d2f4985fa2c4` |
| `OriginalProviderPublicationCoverageTrace.lean` | `9e2578c3e96f95d335263d1c0ed874af36ed411676fbb4977676314a28af56e1` |
| `original_provider_reify.rs` | `39be34a6c0ae2eea673af07dd427e9316f72290687cc937ba2faa13615067729` |
| `provider-publication-coverage-20261027-proof.md` | `1e8a587ae92f342e14af57164c11da7ea5971f7f1fc851300741c78efea1c03c` |
| `provider-publication-coverage-20261027-source.md` | `5bf9efb8f9113675390424ad20e00bd651788c9764068411f92ef9cb4d651594` |
| `OriginalProviderSourceSolution.lean` | `3bf66649fdf4baacb3140de7786165db0d2b138087ca582bd32008b87a95a21a` |
| `OriginalSourceGeneration.lean` | `126a7f2d8336aa7dd2fd4a50cae3eb6b56b6646f7dcf0207130b2a9c209aa7ef` |
| `OriginalSourceEnvironment.lean` | `0e12d33d1b912820324f5140fbe3f16983d0b7ef33137642aaef07faa573f132` |
| `OriginalSourceSyntax.lean` | `3184d156d661ace7da0345f5fa63f8a4396d9f52c745d265239c8d3db1e7d0d1` |
| `OriginalSourceInterpretation.lean` | `feddd8155e6130279c202453e4562019fde5c0ad0f3a0a491dcbc0cb4ef572ef` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `crates/yu-hir/src/module/source_exports.rs` | `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179` |
| `crates/yu-syntax/src/full_parse.rs` | `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93` |
| `proof/call-7.log` | `5fbfda4813f723e607db6efdf9e195e29359b3d910ef6377d50c361eca13d6fb` |
| `proof/call-8-input.lean` | `92bc8ae3b6e88b3913307031d414b39b08c8eb0eb1868fdcd4aa197e52c238f1` |
| `proof/call-8.json` | `13865dbb7de671ddba18d6ea131a512b870e1d4dfa6818a03aadc491b0879f94` |
| `proof/call-8.log` (empty) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `source/attempt2.stdout` | `47fac61ed367741e28dc4fbf3ed2464f346e03b4f97a3e914733e7521982cb6f` |
| `source/attempt2.stderr` | `a46dbcd864945ebdf9c678e34ebecfdc07914ac058747d5f016b95082e0745f2` |
| `source/attempt2.time` | `0ab5d8c9e3e2856caefbe46931810961366a3172bca1bf47babd0f5d5b43906c` |
| `source/attempt2.status` | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |

Short Lean filenames resolve under `notes/theory/lean/YulangClosure/`, except the audit under `notes/theory/lean/`; handoffs resolve under `tasks/agent-loop/inbox/`, adapter under `tools/inline-authentic-extraction/src/bin/`, and receipt paths under `/tmp/yulang-provider-publication-coverage-20261027/`.

Checks by reviewer: static source/definition/test reads and byte hashes only. Lean/Lake/Cargo/tests/formatters/Git/network/descendants: zero. No scratch or generated output written. Sole write: this review file. **Writes stopped** after freezing this revision; no process or descendant remains. Primary owns adjudication, further grants and integration. All parent gates remain **OPEN**.
