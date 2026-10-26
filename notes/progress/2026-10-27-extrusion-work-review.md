# Independent review: original extrusion Work producers

## Verdict and scope

**PASS for the explicitly scoped executable Work projection and local computed
producer theorems.** No blocking proof, theorem-statement, axiom, or overclaim
issue was found within those limits. The independent direct check passed, and
the complete-origin audit accepted all **950 declarations**, **363 theorem
constants**, and **41 authored theorem roots** with no diagnostics or extra
axioms.

This is not a proof that a native source extrusion reaches these states,
finishes all its selected bounds, or supplies the NQ successor. Authentic
native-state extraction and full-operation composition remain open. The note
states those limits, including the supplied in-progress Function frame and
external allocation/resource readouts. All four original whole-language
obligations remain open.

The reviewer is the soundness/hygiene lane, independent of the Work author.
Only this review and `/tmp/yulang-extrusion-work-review/` were written. No
proof source, Rust source, shared status, root import, Git state, build/cache,
`.olean`, or other worker's file was changed. No child was used.

## Frozen inputs and inspection

| Input | SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/OriginalExtrusionWork.lean` | `c419675d75a2cdf03fe5b1ba8d2eef106fea0c4f5187f9f5c06999fa734edd58` |
| `notes/theory/2026-10-27-original-extrusion-work.md` | `7ddec38b70100c0fbc6a2e7c99047cf50d9676170a9f553caa23b2014df746c4` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |

All 1,092 Lean source lines and all 460 paired-note lines were read. The
reviewer inspected all 41 complete kernel-printed authored theorem types and
the complete-origin type/axiom inventory. Native comparison covered the full
`candidate_extrude` Work loop, endpoint-term reconstruction, copied-bound and
physical insertion, `fresh_value_at_level`, `fresh_effect_at_level`,
`retain_extrusion_parent`, representative fallback, source qualification,
capture registration, and the first/later bound-origin loops. Arena inspection
covered raw Term lookup, fixed pages, `positions`, `intern`, `push`,
`require_function_children`, `matches_endpoint`, and `with_term_events`.
The imported immutable-Cell/`ValueUses` definitions and NQ note sections 5.1,
5.3 and 6.1 were checked against the scope of the new claims.

Exact native/dependency input hashes and frozen source/note copies are retained
under the scratch directory. Every recorded input hash was reverified at the
stop receipt. No provisional prelude calculation was substituted for the real
imported target or for this module's audit.

## Eight Work constructors and actual control order

| Native Work | Represented behavior and cut |
| --- | --- |
| `Visit` | Either memo skips repeated work; rows use their selected side and level; structure reads exact ports. |
| `Function` | Rebuilds all four children in native order, retains their kinds and polarities, validates construction, publishes the Function, then remembers it. |
| `Tuple` | Performs the actual slice and missing-child checks; unchanged completion is computed; changed construction is an explicit external call. |
| `Record` | Preserves field data at the changed-call boundary and distinguishes receipt/slice failures; unchanged completion is computed. |
| `Variant` | Preserves alternatives and payload order at the changed-call boundary; unchanged completion is computed. |
| `EffectView` | Requires the memo-selected result to be an Effect row, then stops before view reserve/remapping and memo publication. |
| `Bound` | Reads the actual selected child's rows-first memo and constructs the complete original/insertion/destination/operation request; stops before its insertion owner. |
| `IncomingAllowance` | Reads the actual copied source, then stops before remap, copied-bound insertion, transfer, and initialized-allowance bookkeeping. |

`select` implements `work.pop().or_else(|| pending_bounds.pop())`: a structural
item always wins. Both stacks remain represented and are popped before their
body executes. `initializeLocal` clears only operation-local row/structure
memos, stacks and tuple ports. `start` begins after native occurrence creation
has supplied the operation record; it does not prove `begin_candidate_extrusion`
or source extraction.

Rows-first lookup is retained independently of the initial either-memo skip.
Low rows are remembered unchanged and their bounds are not visited. High rows
allocate at the checked vector-length ordinal, retain the parent, memoize the
row, perform the opposite source link, and only then schedule selected work.
`memo_precedes_link_call` injects an actual pre-append link failure and computes
the already allocated/memoized state. It does not supply an origin fiber or a
successful selected Bound as a premise.

The selected list contains direct rows before exact atoms; positive selects
lowers and negative selects uppers. The opposite source link leaves the
selected side unchanged, as separately proved for Value and Effect. Native
reverse iteration and two pushes yield `Visit` then `Bound` in pop order for
every old entry. The raw source bound is retained even when the child key is
canonicalized. The positive Effect capture traversal is separately reversed
into stack order and precedes those selected-bound jobs. Its row-to-row source
link cannot match the negative row-to-Allowance capture-registration case.
The actual linked capture traversal and its completeness remain external
readouts; the finite supplied list is not asserted to extract them.

`retain_does_not_merge` agrees with the local native owner: parent recording
preserves old levels and representative functions. Its result does not exclude
settlement, rollback, or other representative changes in an enclosing native
history. Native parent comparison/source association and qualification must
still be connected to `Operation` at extraction time.

## Four Function ports, labels, and publication

`functionKeys` reads argument Value with opposite polarity, argument Effect
with opposite polarity, result Effect with the parent polarity, and result
Value with the parent polarity. Their actual raw term IDs remain in
`FunctionTerms`. `function_keys_have_four` derives the list length from the
computed result. Function visitation pushes its completion frame and then
visits the four children in native pop order.

`rebuildOne` reuses the original raw term for an unchanged endpoint. A changed
row is interned with both kind and live-variable polarity; a changed structural
endpoint retains its existing raw term label. Unsupported changed endpoints
fail. `matchesCell` corresponds to the represented cases of the native
Function-child guard, including the rejection of source Component cells as
branch live-variable children. It validates all four ports before final
Function publication. Missing memo entries and malformed child shapes remain
explicit failures.

The corrected representation separates raw labels from allocation chronology.
`terms` contains explicit `(raw label, StoredCell)` pairs and `termAllocations`
is a separate count. `termLabel` is an allocator readout, so no theorem equates
raw IDs with dense list positions. This matters because native Terms carry a
lineage brand and page-based index, with 256-slot pages and a branch directory.
A colliding supplied label produces `invariantViolation`; the note accurately
identifies this as a projection invariant boundary, not a new Rust availability
check. `cell_constructor_readback` and `cell_constructor_immutable` derive
readback and preservation from the equality for the computed constructor;
they do not assume either conclusion or a freshness proposition.

Arena correspondence remains substantial. Native `lookup` can see the
immutable collected prefix as well as branch pages, while `positions` is a
branch-local interning index. The local directory equations alone do not prove
that visible cells have the same interning eligibility, nor do they establish
brand ownership, page visibility, source Component mappings, or the allocator
readout. An authentic source application must account for these distinctions;
this review does not treat `internCell` as an unconditional simulation of every
native lookup/intern state. The supplied computed examples do not claim that
extraction.

`Computed.function_rebuilt` starts from the explicitly supplied in-progress
Function frame with four copies already allocated. It computes the four live
row cells at labels 4096–4099 and the Function at 4100, including all exact
readbacks and structure memo. `negative_copy_in_function` applies the existing
immutable four-port occurrence theorem to those computed readbacks. It does
not replace the Function by a Value-only pair. These results do not establish
the preceding full native copying history.

## Errors retain the represented committed state

Fresh row allocation reserves before appending; failures summarized before
that publication leave the represented row vectors unchanged. Parent/memo/push
and aggregate reserve/accounting gates retain their existing projected state.
The source-link gates surround the actual physical append: an error after the
append retains it. Physical insertion deliberately appends duplicates, matching
the source owner rather than silently deduplicating vectors.

Changed row terms and final Function construction have separate pre-publication
and `constructAfter` gates. This matches `with_term_events`, which first runs
the constructor and then samples recorded capacity events. A sampling failure
can therefore occur after cell publication. The concrete
`post_publication_failure_retains_cells` calculation retains all five published
cells while leaving the structure memo absent. Its supplied readout is not a
proof that a particular native execution reaches error code 17.

Capacity-only mutations, native event arrays, resource accounting, and error
precedence inside pre-publication failures are outside the projected state.
`Funding` supplies returned observations at those boundaries; `funded` merely
chooses all-success observations for the computed examples. Its ghost `calls`
index is not asserted to count every native allocation or sample. No error
branch is converted into normal completion and no rollback of published cells
is inserted into these forward computations.

## Exact Bound producer and remaining composition

`selected_bound_dispatch` assumes an actual `select` equation and the selected
child's memo equation, then derives the `step` result with a computed request.
`bound_dispatch_from_pending` discharges selection for the actual pending head.
Neither theorem takes a complete request, completed extrusion, path, or fiber
as a certificate. The request retains three distinct bounds: the raw selected
`original`, copied-owner/memo-endpoint `insertion`, and representative-read
`destination`. It also retains the whole operation and `capture = true`.

`Computed.row_bound_produced` computes a complete three-step local prefix:
high negative row allocation/link/scheduling, low selected child visit, and
Bound dispatch. Its request keeps the symbolic complete caller. Its state is
defined by the computed prefix, and the theorem additionally proves the exact
external outcome, row levels, row memo, original key, and destination key. It
contains no supplied copied fiber or assumed drain completion.

The actual native application order is:

1. Select Work and obtain its rows-first copied endpoint.
2. Run `candidate_insert_copied_bound`. Its owner performs admission and the
   physical append, then optional capture registration, evidence emission and
   sampling before returning.
3. Run `candidate_transfer_bound_origins`' first loop over the captured source
   fiber head and saved-next links.
4. Run that function's later origin-metadata loop.

Capture is therefore before the first fiber loop; the later metadata loop is
a different owner. The Work module stops before step 2. The accepted separate
key/fiber clients start at their own physical state and do not by themselves
connect all four stages. The join must use the same request, same native
history, actual insertion result, preserved representative readouts, and the
actual state at the first-loop cut. This is not satisfied by selecting an
unrelated physical state after seeing a local loop result.

Both-stack exhaustion similarly stops at `External.finish`; native occurrence
finalization, initialized-allowance replay, final resource sampling, and local
scratch cleanup have not been simulated. Changed aggregates, Effect remapping,
incoming allowances, authenticated sources/qualification, capture traversal,
physical evidence/fiber history, and arena readouts retain separate owners.
A normal whole-operation theorem that every selected Bound completes is still
required for NQ section 6.1. `runPrefix` returns an unfinished state at zero;
it is a finite observation evaluator, not solver fuel or inference termination.
No anchored successor, first empty drain, infinite execution, finite source
allocation universe, fairness premise, or original termination conclusion is
claimed.

## Independent verification

Actual imports were supplied by the parent's successful 15-job focused build,
recorded in `/tmp/yulang-extrusion-client-build.log`. The independent checks
used the real frozen Work module, not the author's audit output or a provisional
interface. The authoritative exits below were directly observed and saved.

Pinned executable:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`;
Lake `5.0.0-src+eb6cafb`. Working directory:
`/workspace/scratch/dd0ca2ec982a/yulang/notes/theory/lean`.
Both checks used one worker, a 120-second bound, and no output-object argument.

| Invocation | Arguments after the pinned executable | Exit | Seconds | Diagnostics |
| --- | --- | ---: | ---: | ---: |
| 1, direct source | `env lean -j1 -M1024 YulangClosure/OriginalExtrusionWork.lean` | 0 | 5.722 | 0 |
| 2, complete-origin audit | `env lean -j1 -M2048 --root=/tmp/yulang-extrusion-work-review /tmp/yulang-extrusion-work-review/Audit.lean` | 0 | 3.414 | 0 |

Two of four authorized compiler invocations were used. No compiler failure or
retry occurred in this independent packet. No further optional check was run.
Default-target integration remains parent-owned and is not claimed here.

The audit used actual module origin (`getModuleIdx?` / `getModuleIdxFor?`),
covering all private, generated, inductive, constructor, recursor, definition,
and theorem constants. Each complete explicit type and transitive axiom set
was printed. It also explicitly `#check`ed and `#print axioms`-checked all 41
authored roots, independently enumerated from the frozen source. Their full
printed types were read; namespace abbreviations used only for display did
not alter the saved exact types. The 950 records contain 508 definitions, 47
constructors, 16 inductives, 16 recursors, and 363 theorem constants. There are
no originating axiom declarations, elided types, `sorryAx`, checker bypasses,
or transitive dependencies outside the three standard axioms below.

| Transitive axiom set | All 950 declarations | All 363 theorem constants | All 41 authored roots |
| --- | ---: | ---: | ---: |
| None | 737 | 257 | 4 |
| `propext` | 201 | 94 | 27 |
| `propext`, `Quot.sound` | 11 | 11 | 9 |
| `propext`, `Classical.choice`, `Quot.sound` | 1 | 1 | 1 |

## Evidence and stop receipt

All evidence below is in `/tmp/yulang-extrusion-work-review/`.

| Evidence | SHA-256 |
| --- | --- |
| `direct-01.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `direct-01.json` | `5fd0e0342e3688c53c19bf8c2081d948dbc76302d78800782b70aa508aac0979` |
| `Audit.lean` | `022c633e962be3e6bc67e30c63c6cc252ba865f06a2b6e80f3596eb7f8ce55d0` |
| `audit-02.log` | `683a62165874fec03fa1d16015b6219eb3d9116a5b447f7235bb58c99eae7d33` |
| `audit-02.json` | `e8a60b37869aa7a00b14f6a5f78b025a2d18c1c79443085a4e113d619ad3bbde` |
| `complete-census.json` | `2961e68b944839e0460464f120e5c50d5c80fc91e0ecb95a94bec3a9869a79f9` |
| `authored-theorem-types.json` | `fe23d9ad09554cbfaf1a5b6abf5a1c42e57dbfd85f661174107cec67574b205d` |
| `axiom-groups.json` | `4cabb4bde274b2aa7eef1bb2a648d5b14744f9375cdafe7fdf4120af34ec0953` |

`checks.json` consolidates actual exits, counts, groups, source hashes and open
application owners. `freeze.json` records this review's hash and stop metadata.
No checker remains active. Work source and note remain exactly frozen at the
hashes above. **WRITES_STOPPED** for this Work packet at the timestamp below;
any later task has a separate exact lease.

Stopped at 2026-10-26T22:58:44.927826+00:00.
