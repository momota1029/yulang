# R62 fresh independent review — BOUNDED PASS (research only)

Assignment `/root/r62_review`, report revision 1. Contract revision 2 SHA-256 `22dadec356ec91d6d575f771aadb5f9f82104b528dd7992500775b48fe8662da`; admission SHA-256 `66773f3c209f4f401eb0065cb69c709eebe4e8d8e5482266aff0a7fcfcdc7687`. Baseline `437716cc057368932fc233809960ae0f378f9e60`. Requested role/model/effort: compiler_referee / Sol / low; observed model/effort UNKNOWN/UNKNOWN. No descendant.

## Finding disposition

BLOCKING: none. Major: none. Minor: none within the admitted bounded claim. This accepts a finite computed policy construction and a behavior-preserving native extraction. It does not certify a source-instance theorem, native compilation/runtime, or production.

The change addresses the responsibility owning the remaining model policy input: owner-local inventory reads now construct the first-entry receipt, rather than requiring an independent Internal callback. The Rust change exposes the existing unique completed source-drain selection at its existing owner. It is not a claimed repair to a previously demonstrated observable compiler bug.

## Independence and frozen evidence

I read the current Rust entrypoint/guards, R62 proof construction, and R45/R47/R55/R57 definitions before reading either author's self-explanation. Later author handoffs were used for frozen audit evidence and claim reconciliation, not as initial correctness evidence. Governing sources included root AGENTS.md/AGENTS.pre-sprint.md, design-authority rules, the Authoritative 2026-10-11 inference principles, sprint/admission, and the original source-preservation obligation. I applied yulang-lean-proofs as a read-only receipt audit; the explicit review packet excludes checker reruns and descendants.

Independently rehashed the five Rust inputs and all eleven imported Lean modules: every current byte hash equals its contract/freeze pin. Rehashed Rust/proof handoffs to `7cfa00da6b3aff81fdd06f17750017714d6681d1cc6bebf1a6e95185fdfca7c2` / `fe0ec65cea32eaefffd66e0e6f4a8b56191425001f977d099ae17012bddff297`. The reviewed R62 module is `e76e41a853673e75555cc5e603f1f84c456332794980613c554a2d69af8d976e`; context is `962af7c44b2e57ba50b7738e82785bd68b517e881ba08ea41c544c9314d60021`; receiver is unchanged `3b60a58a1dba75b908607d91a76f49403314d3667a07987e29fc30fc4a7907e5`.

The primary supplied the exact baseline-to-frozen candidate_context.rs diff in a parent message after my direct source read. It adds only the private evidence type and extracts the previous root scan/receipt guards, replacing its tail with the same ancestry invocation and output construction. I assessed that diff independently; I did not use Git. Native preservation below is grounded in that diff plus current source, not the Rust author's narrative.

## Native guard and ownership attacks

- `lib.rs:18270–18411`: the exact DefinitionUseId, cause, occurrence, source/target definition records, routed-position membership, unique Internal route and admitted slot-0 fact endpoints are checked before permission selection. Registration plus computation role, target owner and recipe root component select the constructor; shared Function/entry images do not select it. Missing or duplicate eligible recipes reject; invalid out-of-range registrations are skipped, matching the unchanged native loop. The selected constructor's source lambda/parameter, recipe, unique origin, positive Function child, negative effect entry, slot-2 fact and retained permission are independently authenticated. No spelling or path participates in this new logic.
- `candidate_effect.rs:607`: permission selection remains by the same registration, with exact parameter/formal/owner/scope/occurrence/entry and nonempty complete permission vector. `candidate_receiver.rs:618–679` still restricts the experiment to its actual singleton use and exact receiving/target schema owners, then reads the addressed live lower-row/lower-atom slot. Constructor readback is never substituted for that live read.
- `candidate_context.rs:3132–3165`: indexed emission, indexed admission, bound/readback/current agreement, correct entry owner/lower lane, unique physical-slot emission, relation presence and relation pair all precede source-root selection. The primary's exact diff shows these guards and variants unchanged.
- `candidate_context.rs:3169–3197`: root candidates are selected by occurrence and typed relation pair before any completion/drain filtering. Thus two matching origins reject as AmbiguousUseRoot even if only one has a valid receipt; a bad receipt cannot select a different root. Missing root/receipt, incompletion, wrong origin index, created/selected relation, incoming/replay receipt, cause occurrence or task pair reject as MissingUseRoot. The private evidence value is constructed only after these checks. The helper is immutable and retains no new history or allocation.
- `candidate_context.rs:3163–3165` and `3199`: unchanged directed ancestry runs immediately after the precheck; invalid relation indices and bounded visitor failures remain owned by the existing ancestry reader. A stale/wrong current slot or foreign relation cannot be repaired by ancestry.
- `candidate_receiver.rs:162–179`: first-entry current_internal_emission (including ancestry) still precedes the outer emission/admission/slot/bound identity comparison. Later physical edges keep the already chosen use root and require directed ancestry. Catch uses the separate None-entry route and does not acquire an Internal obligation. Support-member traversal and inconsistent entry/use-root/step shapes retain their existing branches.

Concrete alternate traces checked statically: duplicate roots with one completed receipt; correct root with wrong cause/task; same contents at a foreign physical slot; wrong lower-lane owner; missing admission before inner bound mismatch; invalid ancestry plus outer admission mismatch; missing Internal inventory in Catch; same Function image at another registration/owner. None exposes a new acceptance or changed native failure order in the extracted code. No mutable state/restoration, AST/CST, or IR phase boundary is modified by this extraction.

## Lean construction and quantifier review

R62 lines 16–45 compute ownerSelection/sourceProbe from primitive inventories. The caller supplies request coordinates, not a Probe or successful certificate. Missing/duplicate roots and eligible recipes are not silently skipped. Lines 54–62 enforce the full existing R45 OwnerReads and Identity plus the actual parameter-recipe equation. The source/native request construction remains an explicit source obligation.

Lines 71–86 are exactly R47 Matches with only its ancestry conjunct removed. Lines 101–143 compute this certificate after source incidence/artifact/entry, selected stored emission, live slot, indexed admission, readback/bound, unique slot event, relation and unique drain-root reads. A final decidable BeforeAncestry check enforces every remaining R47 clause; any failed clause returns an error. Lines 160–187 project current-slot/source-root equations and reinsert ancestry.

Lines 191–199 use `BoundedAncestryR61.native base records` both in the Internal policy and R60 constructed readers. Lines 207–224 apply the consumer on `inputs` of that same Native, preserving arbitrary S/T, DecidableEq instances, inventories, records, request, per-query resource schedule and Search. Its successful modeled outer Run, Checked goal and terminal endpoint remain premises. The callback-free candidate iff preserves the existing R58/R59 target quantifiers.

Lines 240–272 existentially recover the Root from actual successful readRoot inside successful first-entry policy, then derive R45 extraction and R47 Matches using the actual successful R61 ancestry witness. The main success result does not merely accept a constructor-authored Root. Conditional Root projection lemmas are used through this computed success theorem. Lines 286–332 preserve failure-before-ancestry, ancestry-before-outer-identity, later-entry direction and Catch bypass. The two R58 phases remain distinct; a reflexive/empty-path successful Run is not mislabeled as a first physical-entry receipt.

The fixture equations at lines 343–395 cover real computations over the admitted finite fixture, including missing/duplicate permission/construction/root, foreign owner/use, stale/wrong slot, wrong cause/incompletion, and ancestry failure before outer mismatch. They are not Rust execution evidence. I also read the relevant existing Rust tests at candidate_receiver.rs:3163–3255 (signal suppression, distinct same-spelling family forwarding, grouped scrutinee, and unsupported-envelope controls); none was changed or run.

Lean failure cases intentionally group native errors: missing/ambiguous source root can both become firstEntry/missingInternal, and several drain checks become firstEntry/boundMismatch. The model proves its critical stage order; it does not prove an exact Rust error-variant simulation. Exact native variants/order are supported only by the native extraction diff and source analysis above.

## Audit authentication and completeness

The full local import closure has exactly eleven existing modules: R39, R45, R47, R48, R49, R55, R57, R58, R59, R60 and R61. Each source pin matches revision 2. I decompressed FINAL-R3's in-memory program and independently authenticated input SHA-256 `6abd25bfd1e8b12b4060131dba8a3b1e77456744d15439b15c122bac681bc87e` (235163 bytes) and complete stdout SHA-256 `fe5f5176b771aadbd9a51b7adf56b3eff917b431cc8e843d318d34fcf1bf5658`. The entire frozen R62 body is verbatim in that program, with only its import removed.

The inherited R61 receipt rehashes to `95d2f3c293eccd2140460399b5011ad38c97480e5d66b67b2769a8004261ccff`; its reused stdin authenticates as `18b44e56868be57a9ba7820f7ba3395be004af70252c779caf240b52e627d1a6`. All 245 inherited byte-span manifest hashes match original source. Reconstructing each imported module by removing only manifest-declared omitted unused theorem spans and imports yields a verbatim contiguous slice in FINAL-R3 for all eleven modules. The full R61 body is retained. No changed definition/theorem interface is substituted. The program's non-audit directives are import Std, Elab.async false, compiler.extract_closed false, and pp.all true; none disables kernel checking.

FINAL-R3 reports native Lean 4.35.0, `-j1 -M1024 --stdin`, exit 0, no warning/stderr/timeout, 9.974s wall and 1021968 KiB peak child RSS. This is authenticated retained author-run evidence, not an independently rerun checker. The repository pin remains Lean 4.35.0 with no external packages. No default/module import build was run in this review or claimed by the final sliced-stdin audit.

All 38 named authored declarations reconcile with the source census, including all 19 theorem roots. Every one has exactly one complete type and one full transitive axiom report in FINAL-R3. Fully expanded exact types and unabridged axiom reports are retained in the frozen proof handoff's `R62-FINAL-R3.stdout` field (JSON block beginning at line 764), authenticated by the hash above. The table below records each exact source type locator and the complete axiom set, without dropping hypotheses or eliding an axiom tail. Global parameters for the generic source declarations are `{S T : Type} [DecidableEq S] [DecidableEq T]`; fixture declarations specialize to Nat. No root depends on Classical.choice, sorryAx, a project axiom, or a native shortcut.

All source type lines below refer to `notes/theory/lean/YulangClosure/InternalRootPolicyR62.lean`.

| Declaration in YulangClosure.InternalRootPolicyR62 | Kind | Exact type at source line | Full transitive axiom set |
| --- | --- | ---: | --- |
| `Source` | abbrev | 10 | `none` |
| `Request` | abbrev | 11 | `none` |
| `ownerSelection` | def | 16 | `propext` |
| `sourceProbe` | def | 31 | `propext` |
| `Incidence` | structure | 45 | `propext` |
| `incidence` | def | 52 | `propext` |
| `rootQuery` | def | 61 | `propext` |
| `BeforeAncestry` | def | 66 | `propext` |
| `Root` | structure | 84 | `propext` |
| `readRoot` | def | 94 | `propext` |
| `Root.receipt` | def | 132 | `propext` |
| `internalRoot` | def | 136 | `propext` |
| `source_incidence_checked` | theorem | 139 | `propext` |
| `root_current_slot` | theorem | 143 | `propext` |
| `root_source_fields` | theorem | 155 | `propext` |
| `complete_after_ancestry` | theorem | 164 | `propext, Quot.sound.{u}` |
| `policy` | def | 174 | `propext, Quot.sound.{u}` |
| `readers` | def | 178 | `propext, Quot.sound.{u}` |
| `same_inputs_decoder` | theorem | 182 | `propext, Quot.sound.{u}` |
| `callback_free_candidates_apply_consumer` | theorem | 187 | `propext, Quot.sound.{u}` |
| `computed_internal_success` | theorem | 205 | `propext` |
| `first_entry_success_has_both_certificates` | theorem | 219 | `propext, Quot.sound.{u}` |
| `root_native_projection` | theorem | 262 | `propext` |
| `source_failure_precedes_ancestry` | theorem | 273 | `propext, Quot.sound.{u}` |
| `ancestry_failure_precedes_outer_identity` | theorem | 289 | `propext, Quot.sound.{u}` |
| `later_entry_has_directed_ancestry` | theorem | 306 | `propext, Quot.sound.{u}` |
| `catch_keeps_existing_policy` | theorem | 316 | `propext, Quot.sound.{u}` |
| `callback_free_candidate_iff` | theorem | 323 | `propext, Quot.sound.{u}` |
| `fixtureRequest` | def | 339 | `none` |
| `fixtureRecords` | def | 340 | `none` |
| `fixtureSchedule` | def | 341 | `none` |
| `fixturePhysical` | def | 342 | `none` |
| `fixtureBranch` | def | 343 | `none` |
| `computed_fixture_receipt` | theorem | 345 | `propext` |
| `computed_fixture_first_entry` | theorem | 349 | `propext, Quot.sound.{u}` |
| `computed_fixture_missing_duplicate_and_foreign` | theorem | 353 | `propext` |
| `computed_fixture_stale_slot_and_drain` | theorem | 370 | `propext` |
| `computed_fixture_ancestry_before_outer_mismatch` | theorem | 382 | `propext, Quot.sound.{u}` |

## Remaining obligations and stop receipt

Rust-to-the-same-Source/Native/Request inventories and actual outer successful Run remain OPEN, owned by Luna/source correspondence. This includes actual singleton-use/schema coordinates, store/artifact branding, raw/canonical fact endpoint equations, physical indices, pointer-to-Nat, and full program root extraction. The finite reader does not construct arbitrary request coordinates or prove equality to an independently supplied entryRoot. Arbitrary repeated-call allocator/resource/failure equivalence, Context/R50, R51/publication, native runtime, original A/B, whole soundness/effects/principality/termination/hygiene and production remain OPEN. No narrowing of original source scope or original shared witness follows from this bounded pass.

Checks performed here were source/receipt reads, hashes, decompression, import enumeration and static byte/type/axiom reconciliation only. No build, tests, typecheck/checker rerun, Cargo/Lake, Git, scratch/cache/target/environment/worktree, or descendants. Only this leased report was written. Elapsed review time was not independently metered; the 1200s assignment bound was retained.

Worker state: STOPPED. WRITES STOPPED. No active subprocess or descendant; no additional lease or write claimed. Primary adjudication/integration remains pending.
