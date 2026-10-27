# Provider source solution — independent frozen review r1

Reviewer: `/root/provider_source_review`, fresh non-author compiler referee.
Contract: `PROVIDER-SOURCE-SOLUTION-REALIZATION-20261027/r1`, SHA-256
`1cfca56787f12978599498702021546ac0ebb259554848a58a23df8b36fbdf2f`;
amendment 01: `b1b9bc2ecc8a268cca8118b7bab1d9ea2c06a52215c4732b2e4d748d548a1bc1`.
Requested role: `compiler_referee`; effective model/effort and session UUID:
UNKNOWN from the exposed runtime metadata. No descendant was started.

**Verdict: INCOMPLETE; reject acceptance of the fixed constructive outcome.**
The main finding is PSR-R2: under original nonempty Return admission, open
replay and an empty prior map, a finite Return-list extension misses admitted
fresh-occurrence branches and cannot construct the required provider judgment.
This blocks this proposed construction; it does not refute the original provider.
The source adapter does not compile, no trace exists, and the proof constructs
conditional source-constructor/map algebra rather than an authenticated provider
solution in that map. The required final theorem type/axiom audit was not
obtained. This is not an observed Rust/source semantic counterexample and does
not refute the original inference parent. All parent gates remain OPEN.

## Frozen bytes and evidence method

Independently rehashed all 38 direct contract pins: all match. The source and
proof outputs and handoffs currently hash as follows:

| Path | SHA-256 / disposition |
| --- | --- |
| `tools/inline-authentic-extraction/src/bin/original_provider_reify.rs` | `5ed03633e8a37775847d7c28fc08d2d7acc98965299e0dbe27568b266fd2b8ed` |
| `notes/theory/lean/YulangClosure/OriginalProviderSourceSolutionTrace.lean` | ABSENT |
| `notes/theory/lean/YulangClosure/OriginalProviderSourceSolution.lean` | `3bf66649fdf4baacb3140de7786165db0d2b138087ca582bd32008b87a95a21a` |
| `notes/theory/lean/AuditOriginalProviderSourceSolution.lean` | `693e0451a4bdf44512935020805f419f44cfa2858dff7d473766d3aabd84015c` |
| `tasks/agent-loop/inbox/provider-source-solution-20261027-source.md` | `af5a24838d5ce9a58a077a8f4e31b9deefd8e656096e3d757a82a906d2ed0f3a` |
| `tasks/agent-loop/inbox/provider-source-solution-20261027-proof.md` | `9534690e187ce42d77906c86734ad83820ad53531f31d1e1efae6e7cf0f28aae` |

Read the actual adapter, theorem and audit sources, original source syntax,
generation/environment rules, the governing Source-Generalize design §2 and
construction §§3–5, original parent §1 and birth-level correction, inference
principles, actual HIR ownership/import constructors and relevant import test.
Producer explanations are not evidence for their claims: compilation, build and
audit dispositions below are checked against retained command output/metadata;
mathematical scope is checked against actual definitions and theorem statements.
The Lean skill's audit guidance applies; no Lean/Lake, Cargo, test, formatter or
Git process was invoked by this reviewer. Baseline Git identity remains the
primary's observation, not an independently authenticated child Git claim.

## Findings

### BLOCKING PSR-R1 — provider Source/Context provenance is not constructed

Locations: `original_provider_reify.rs:76`, `:133`, `:239–255`, `:305`, `:334`;
`OriginalProviderSourceSolution.lean:17–35` and `:63–67`.

The frozen Rust file still has ambiguous `parsed.source().as_ref()` indexing
and moves `provider_export_index` while `provider_export` remains borrowed.
The retained attempt 2 stderr contains E0282 at lines 76/133 and E0505 at 305,
with the later use at 334. It ends with compilation failure and exit 101.
Its independently checked SHA-256 is
`060ae6e9ba89952f4041dc275a8890d522261c30cbd4719727f2022027f3b951`;
attempt 2 stdout is empty and the status-file hash is
`39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c`.
No provider parsing/lowering, foreign-owner rejection, consumer identity join
or trace emission took place in this executable.

The Lean `Occurrences` fields are arbitrary proof coordinates. The source term
and Context extension are calculated from those fields; no theorem connects
them to this exact UTF-8 provider or derives a genuine incoming Context.
`provider_solution_requires_initializer` extracts an initializer judgment from
an assumed full provider judgment. It supplies no independent initializer
semantics. Fixing compilation alone would therefore leave the original missing
Source/Context owner in place.

Required invariant: the sprint's fixed constructive chain begins with
authenticated declaration/formal/body and original Source/genuine Context;
Source-Generalize construction §3.1 uses actual source operands and capture
evidence. Minimum closure: successful bounded execution under a fresh grant,
frozen owner rejection/identity evidence, then an independently justified
mapping to original coordinates and Context plus the actual local admission
and initializer derivation. Do not substitute the inspected resolver test or
an arbitrary `Occurrences` instance for this bridge.

### BLOCKING PSR-R2 (main) — finite completion does not construct the universal open provider judgment

Locations: `OriginalProviderSourceSolution.lean:142–150`, `:247–255`,
`:268–314`, `:321–358`; direct owners
`OriginalSourceGeneration.lean:762–766`, `:773–781` and
`OriginalSourceEnvironment.lean:638–647`.

`finiteCompletion` preserves prior entries and adds the records of a supplied
finite Return list. The membership theorems quantify only over that list;
`compatible` and the list's admission are explicit inputs. No conclusion
constructs `SourceJudgment` in the completed map. `completion_preserves_original_readout`
is only equality of `decode` and equivalence of `Admitted`, both independent of
the publications field. Full source judgment additionally checks publication
lookups, actual Shared admission, atoms, checking and all initializer/body
premises. Those do not follow from the readout equation.

There is a concrete quantifier obstruction to treating finite-list completion
as the missing open judgment. Keep the original `Admitted` interface and an
open replay state. If one Return payload is admitted after `enterInitializer`,
the same payload with the same parent path is admitted at every natural-number
occurrence: `Admitted` tests the parent path and decoded `DataAdmitted`, which
does not inspect occurrence. This also follows directly from
`admitted_scoped_iff` (`OriginalSourceEnvironment.lean:649–661`). With an empty
prior publication map and any finite list, select an occurrence absent from
that list. The publication key includes this occurrence through the Return
exit path (`OriginalProviderSourceSolution.lean:89–100`, `:212–216`), so the
completed map returns `none` for this admitted branch. Yet `executionOpen`
requires the branch for **every** admitted candidate, and
`provider_solution_requires_fixed_record` would require `some` at that key.
Thus this finite extension cannot construct the open provider judgment in
that setting. This argument uses the definitions and retains arbitrary real
payloads; it invents no successful Kernel or empty Context. It is an abstract
source-rule obstruction, not authenticated evidence that the actual provider
has this incoming map or any admitted Return payload.

Required invariant: the contract and amendment demand the provider judgment
in the same completed graph, retaining original event quantifiers, and forbid
making `publicationValid` true by map replacement alone. Construction §§3.1,
3.3–3.4 retain actual Return/Shared and independently legal provider derivations.
Minimum closure: obtain actual semantic-owner data and establish coverage of
**all** required admitted branches by the original prior graph plus completion,
then derive the complete provider judgment in that very graph. A finite list
of members is insufficient. If the authentic case has fixed replay or an
already sufficient graph, derive those facts at their owner; do not narrow
admission or alter occurrence semantics to fit the list. Return any genuine
semantic contradiction through the existing authority path.

### major PSR-R3 — consumer transport assumes the missing exposure equations

Locations: `OriginalProviderSourceSolution.lean:364–377`;
`original_provider_reify.rs:295–318` and `:183–201`;
`crates/yu-hir/src/module.rs:4817–4838`.

`complete_record_transport` proves Option lookup algebra for the entire record
given the two exact `publicationName` equations and fixed-map equation. Those
equations are precisely the missing source/import bridge; the theorem provides
no relation to Rust's `SourceExportId` or this consumer's actual names.
The adapter has unexecuted explicit/prelude identity comparisons. The existing
test checks exact provider identity equality, not logical publication judgment
or record transport, and was inspected rather than run in this review.

Required invariant: the final chain must transport a complete established
provider record to both authenticated exposures; construction §§3.3–3.4
distinguish source publication, monomorphic alias and actual instantiation.
Minimum closure: derive both logical exposure equations from actual import
owner evidence and the provider's established record, then apply this theorem.
No inference of `Mono`, `Published` or `Family` follows from alias spelling,
visibility, route or export identity. This code does not claim otherwise.

### major PSR-R4 — no delivered theorem has a completed type/axiom audit

Locations: `AuditOriginalProviderSourceSolution.lean:6–200`;
scratch `proof/call-7.log`, `proof/call-8.log`, `proof/call-8.json` under
`/tmp/yulang-provider-source-solution-20261027/`.

The audit source contains theorem-kind checks, full type commands and axiom
collection/rejection for all 15 roots. Call 7's actual log records a successful
targeted build; its SHA-256 is
`00614d5165c76779cd4d5c9c1f259d48d3c5afe6af44425a527cb8e1009e1e58`.
Call 8's log has zero bytes. Its metadata records exit -9 and
`termination = RSS_LIMIT_1GiB`, group peak 1,084,428,288 bytes; metadata hash
`f83a0b0d0b4f9debb698aaed5a415d7fdfdc41319a57492b4fe78c841cc19bff`.
There is no printed type or axiom output for any root. Source signatures and
the successful build cannot substitute for the required transitive audit.

Required invariant: the packet's proof verification clause and Lean skill
require full theorem types and per-theorem complete axiom audits; no `sorryAx`
or project axiom may be hidden in the dependency cone. Minimum closure: a
separately granted bounded audit that completes for these frozen bytes and
records all types and all axiom lists. Current proof budget is exhausted;
this review grants no retry. Static inspection found no new sorry/admit,
project axiom or checker bypass; that is not a transitive axiom audit.

## Accepted limited evidence and boundary

The candidate tuple at `OriginalProviderSourceSolution.lean:102–113` retains
all seven fields of `PublicationRecord` (`OriginalSourceGeneration.lean:524–532`):
identity, entry path/names/frames, captures, completed fixed frames and
initializer snapshots. Return and anchor-selected Shared frames are retained;
the new map gives existing records priority. Same-identity consistency for
listed scoped candidates follows from complete Return-key injectivity, while
consistency with already stored records is explicitly assumed. No conflict at
an actual provider identity was observed.

The source-rule equation and necessary-condition extraction follow the actual
unannotated binding/Lambda construction. Incoming Context, Kernel, Sorts and
semantic payload remain parameters; there is no fabricated empty Context,
successful Kernel, degenerate Sorts or imported trace. The proof does not equate
Rust exposure aliasing with SRC-J `Client.alias`. These are useful, conditional
algebraic results with a targeted-build receipt, pending final axiom audit.
They neither repair the missing semantic/source owner nor establish the fixed
constructive chain. Already-fixed replay, other source forms, recursive groups,
complete Call/effects, import-root elaboration and Rust/native correspondence
remain uninstantiated. Their absence must not narrow the parent domain.

The original parent at
`notes/theory/2026-10-13-intrusion-source-preservation-proof.md:16–44`, with the
birth-level correction, retains all supported source programs, principal
coverage, soundness, progress/termination, original type/event scopes, complete
Call, effect hygiene and shared witnesses. **All those gates remain OPEN.**
No minor correctness finding is recorded. The producer handoffs accurately
label their principal incompleteness; this verdict rejects constructive
acceptance rather than alleging a claimed theorem has been disproved.

## Resource and cessation receipt

Reviewer execution: read/hash/static inspection only; Lean/Lake 0, Cargo 0,
tests 0, formatters 0, Git 0, descendants 0. Sole write is this explicitly
leased review artifact; no source, proof, scratch, cache, status or other path
was edited. The proof worker's reported unleased `__pycache__` output remains
primary-owned cleanup/adjudication; this reviewer did not touch it.

Review revision 1 is frozen after this write. Writes stopped; no descendants
or background processes were started. The file's SHA-256 is returned separately
to Luna so the file does not contain a self-referential hash.
