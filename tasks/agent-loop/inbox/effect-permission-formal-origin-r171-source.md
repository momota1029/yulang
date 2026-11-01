# R171 source construction and FormalEntry origin

Status: frozen source-evidence handoff; independent review pending.
Disposition: **NO_SAFE_CODE_SLICE**. No reachable constructor bug was demonstrated.
Baseline: primary-pinned `yulang3` / `6dc6aa855`; no Git commands were run by this worker.
Method: static dataflow and constructor inspection on the exact five admitted inputs.

## Authenticated dependency snapshot

SHA-256 was checked before inspection and again before writing this handoff; all
five hashes matched the sprint contract both times.

| Input | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_effect.rs` | `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15` |
| `crates/yu-hir/src/module.rs` | `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646` |
| `crates/yu-hir/src/module/local_source.rs` | `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1` |
| `notes/theory/lean/YulangClosure/FormalEntryPrestateBridgeR169.lean` | `bb0aaffe95f99881b089807a202991c4349a7c61e9ebb0f42f56d7f080a7baf4` |

The governing packet is `tasks/agent-loop/sprints/effect-permission-formal-origin-r171.md`,
especially Fixed outcome, Required construction invariants, and Closure boundary.
Rules read: root `AGENTS.md`, `AGENTS.pre-sprint.md`, `rules/research-lab.md`, its
preserved baseline, `rules/design-authority.md`, and `rules/git-concurrency.md`.
No new language meaning or implementation authority is proposed.

## Constructor facts and derivation

1. **Complete IDs retain ownership.** `HirParameterId` stores private owner and
   ordinal fields, has a private constructor, and compares/hashes both
   (`module.rs:1377–1385,1404–1415`). `SourceRootId` distinguishes Definition,
   Expression, and Member (`1301–1305`). Definition identity compares artifact
   pointer and definition (`1184–1195`); expression identity retains a branded
   occurrence (`1200–1205,1438–1449`); member identity compares artifact, module,
   declaration, member, and kind (`1279–1295`). Equal ordinals from different
   owners are not interchangeable parameter IDs.

2. **The existing header interval is derived, not assumed.** Definition header
   parameters are enumerated from zero with checked `usize -> u32` conversion
   and use the same definition root (`module.rs:3579–3595`). Ordinary binding
   formation receives those actual binding parameters and owner
   (`2553–2557`); the opt-in direct formation path passes the same parameters
   (`3603–3613`). Direct expressions pass an empty header (`2567–2572`). Member
   formation constructs receiver ordinal zero and header ordinals `index+1`,
   checking both addition and conversion (`local_source.rs:991–1022`). Thus the
   union of header and root-parameter ordinals is precisely `[0,n+r)` for these
   call routes, where a member has `r=1`, and a definition/expression has `r=0`.

3. **Later allocations cannot collide with the header or one another.** One
   builder starts `next_parameter` at checked `n+r`
   (`local_source.rs:1107–1115`). Its allocator reads that counter and performs
   checked increment *before* returning the owner-branded ID (`1433–1436`).
   Record field binders, inline Lambda parameters, and local named parameters
   all use this allocator (`1402,2107,2760`). Record fields may consume gaps
   between Lambda parameter ordinals; no argument may assume contiguous
   ordinals for Lambda parameters alone. Exhaustion returns an error before
   emitting an ID; no wrapping ID is produced. This is a mathematical induction
   on successful allocator calls using ordinary Rust integer/Vec semantics,
   not a machine-checked execution theorem.

4. **Lambda forms retain the actual parameter and annotation.** The three
   production Lambda emission sites in this input are header-chain formation
   (`local_source.rs:1146–1184`), local initializer chains (`1297–1313`), and
   inline Lambdas (`2107–2122`). Header parameters retain their given IDs and
   parsed annotations (`1158–1168`); local header parameters retain their
   freshly allocated ID and annotation (`2760–2788`); inline Lambdas have no
   annotation (`2112–2116`). Named local initializers use the stored parameter
   at each ordinal; their work item is appended when the corresponding new
   binding is appended (`2794–2810`), then transferred from `prefix_work` to the
   builder work stack (`2827–2831`). The same lexical spelling can shadow a
   previous spelling without sharing its ID.

5. **Expression indexing and publication are explicit.** `slot` allocates the
   current expression-vector length, checks conversion, appends one empty
   slot, and records the same owner (`local_source.rs:1484–1491`). `set_at_range`
   assigns an expression to that index (`1541–1549`); it does **not** dynamically
   check that the slot was empty. Do not model this helper as a checked
   single-assignment operation. Successful formation rejects any remaining
   empty slot and moves the vector into a `LocalSource` with the same owner
   (`1335–1355`). Occurrence reordering updates only each stored occurrence,
   preserving vector order, forms, IDs, and annotations (`145–162`). Occurrence
   allocation itself uses checked increment (`module.rs:2751–2759`). Public
   accessors expose shared slices/references and validate the owner for index
   lookup (`local_source.rs:169–180`). A global proof of the work stack's tree
   traversal and all crate-internal mutation is outside this static packet;
   there is no claimed general single-assignment theorem here.

6. **Collection retains the origin fields before scheduling.** The collector
   retrieves the HIR-owned LocalSource and requires pointer equality with the
   supplied source (`candidate_source.rs:1052–1054`), checks parent-owner
   compatibility (`1055–1061`), and records/validates occurrence ownership
   (`1064–1069`). For each Lambda in the immutable expression slice, it appends
   the parameter ID at recipe position `recipes.len()`, then appends one formal
   at registration position `formals.len()`, storing the same owner, expression
   enumeration index, parameter ID, recipe position, role and scope
   (`1098–1116`). The shared `push` reserves then appends (`560–563`). Therefore
   each successfully appended registration has its retained recipe and exact
   source index, regardless of any unrelated prefix already in either vector.
   Root receiver parameters receive recipes but no Lambda registration
   (`1082–1090`). Record binders get recipes and an explicit duplicate guard
   (`1119–1123`).

7. **The map needs construction freshness.** `formal_registrations` is freshly
   empty (`candidate_source.rs:1079`), and its only insertion in this input is
   `insert(parameter.id, registration)` after each Lambda append (`1117–1118`).
   The return value is ignored: a duplicate key would overwrite its previous
   registration. The `parameters` map has the same unchecked overwrite for
   Lambda keys (`1107–1108`). The header interval plus fresh allocator above is
   the source basis for excluding those duplicate keys along the mapped
   formation routes; final successful lookup alone does not prove uniqueness.
   R169 `readRegistration` returns the *first* matching list entry
   (`FormalEntryPrestateBridgeR169.lean:52–55`). To transcribe Rust's last-write
   behavior faithfully, prepend map updates or prove unique keys from the
   actual constructor history before equating the lookup results. Appending
   arbitrary duplicate updates to the R169 list would be incorrect.

8. **Action payload comes directly from that immutable Lambda.** The work loop
   reads `expr` from the same source expression slice
   (`candidate_source.rs:1208–1214`); its Lambda branch uses that parameter
   (`1280–1288`). When an annotation with effects is present, it clones exactly
   `parameter.annotation`, obtains the registration from the completed local
   map, and appends `FormalEntry` with that annotation, that expression's
   occurrence and the registered scope (`1323–1327`). No later map insertion
   occurs. In the inspected collector, later formal updates concern
   `receiver_body` only (`1344–1347`). Native preparation checks the recipe
   identity and adds `native_root`/`entry_effect`, retaining the source origin
   fields (`2303–2325`). Dispatch forwards the action fields unchanged
   (`2469–2475`).

9. **Runtime checks authenticate the stored origin, but omit annotation
   comparison.** `candidate_formal_entry_annotation` reads the indexed formal,
   finds its owner's source and stored Lambda index, and checks occurrence and
   parameter ID (`candidate_effect.rs:1994–2001`). It checks owner, scope, recipe,
   source owner, computation role and absence of retained/domain duplicates
   (`2002–2011`). It does not reread/compare the source parameter annotation.
   Equality with the selected source annotation follows from the collector's
   retained origin and immutable snapshot, as a composition of items 6–8;
   it does not follow from these runtime guards in isolation. Permission
   construction copies the resulting annotation/row/owner fields
   (`2020–2030`). Source and native entry identities remain distinct.

## Exact finite inference to prove

Fix one successfully formed, unmodified `LocalSource` from the mapped HIR
construction and one successful registration scan of that same source. Let
`i` be a Lambda index with parameter `p`, and let `j` be the registration
inserted for `p.id`. Derive key freshness by header allocation and successful
allocator history. Since no later registration insertion has that key, the
final map reads `p.id -> j`. Appending preserves the record at `j`, so its
`owner`, `lambda`, `parameter` and `recipe` are the same source owner, `i`,
`p.id`, and appended recipe position. Subsequent action collection at `i`
copies `p.annotation` and the same occurrence. Therefore the source Lambda
selected by that registration owns exactly the action annotation.

The static source evidence establishes which constructor facts the Lean
finite model must capture. It does not itself prove Rust execution realizes
that model or establish full crate-wide mutation freedom. The required
snapshot premise must refer to one shared constructor result, rather than
independently chosen raw vectors/maps/actions. No new bare uniqueness premise
is recommended as an adequate closure argument.

## Discriminating omitted-invariant witness

R169's unrestricted `Raw`, `Collected`, and source-phase guards permit the
following abstract witness: one owner, two expression entries
`[lambda occ (id,A), lambda occ (id,B)]` with `A != B`, one formal at registration
zero whose stored Lambda index is one and whose parameter is `id`, and map
`id -> 0`. Select annotation `A` by `Collected.lambda` at index zero; the
source phase can select index one with annotation `B`, because its occurrence
and ID are identical. Use equal owner/scope, a valid recipe and entry, no prior
permissions/domains, and a row of arity at most one to satisfy the remaining
modeled guards. Thus the annotation join cannot be recovered merely by
destructing R169's successful trace. Two expression slots are needed for this
particular mismatch; one slot gives the same constructor payload on both reads.

This is a hand-derived finite-model falsifier, **not an executed Lean check or
a reachable Rust counterexample**. It intentionally violates constructor ID
freshness. It motivates R171's actual finite registration construction rather
than a new runtime guard or source restriction.

## Checks, resources, omissions and next action

Commands used: bounded `rg -n` symbol searches, `nl -ba ... | sed -n ...`
source reads, and `sha256sum` over the five exact inputs twice. No executable
experiment, random seed, enumeration, mutation run, Lean invocation, Rust
build/test, Cargo, Git, scratch, cache, environment or target was used. The
only created path is this handoff. Searches cover the named constructors and
map mutation sites in the exact inputs; they do not cover unleased files,
annotation parser internals, runtime subtree, external callers, unsafe code,
compiler/toolchain correctness or allocator behavior beyond standard APIs.
Commands were serial and lightweight; process RSS and exact elapsed time were
not measured. Work remained within the 600-second source packet budget.

Recommended next action: prove the append/index/map-origin invariant in R171's
finite constructor model, derive its freshness from the represented allocation
history, and apply that origin to R169's exact selected formal before claiming
annotation identity. A kernel proof remains conditional on the explicit
source-to-model transcription and shared snapshot until those are established.
No change to Rust is justified by this packet.

## Commit packet for the primary

- Exact leased path: `tasks/agent-loop/inbox/effect-permission-formal-origin-r171-source.md`.
- Baseline SHA: `6dc6aa855` (primary pin, no independent Git resolution).
- Changed dependency hashes: none; all five authenticated hashes remain above.
- Claim/review: static constructor correspondence and abstract falsifier;
  independent source review pending; no theorem or production closure claim.
- Checks already run: exact dependency hashes twice, bounded source reads and searches.
- Proposed message: `Record R171 formal registration origin source audit`.
- Deferred shared deltas: primary records NO_SAFE_CODE_SLICE, map-update order
  obligation, source-model/snapshot boundary, dependency hashes and review result;
  no shared records were edited by this worker.
