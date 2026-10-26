# Native dictionary denotation r4 — fresh independent M3 review

Reviewer: `/root/dictionary_denotation_review_r4`.
Producer: `/root/source_membership_r4`; producer writes stopped at
`2026-10-26T11:16:43.895229+00:00`.
Parent-supplied baseline: `37ec9da2aaca2d7b806887d06d9bbd8b0fc5439c`, branch `yulang3`.
Review assignment: fresh independent M3 review of the frozen runtime dictionary
construction and its claimed original-source application. No authorship or repair
contribution to the reviewed proof; no descendants. The supported generic worker
inherits the parent model; no unavailable custom-role execution is claimed.

## Verdict and exact scope

**ACCEPT. BLOCKING: 0. MAJOR: 0. MINOR requiring repair: 0.**

Accept the checked mathematical Word/Substitution DAG construction, its stated
finite dictionary-denotation theorem, and the bounded source-level comparison with
the actual playground runtime owners. The note and handoff accurately distinguish
this result from an executable Rust verification and from original source Function
membership. No producer repair is requested.

This acceptance does **not** close original `ValueMem_F†(W,r,e)`, full `PhiW`, the
original `P_F` phase/observation envelope, descriptor/annotation/history realization,
`SourceT`, or whole-language inference/source-native closure. It does not certify
the native combined work budget, allocation availability, or complete failure-state
mutation behavior. Those are already explicit limits of the frozen submission,
not concealed findings or new restrictions on source programs.

The original scope remains the same independently admitted complete challenges,
actual callable/provider, current event, joint witness, pre-Return interactions,
divergence, pending continuations and compatible future developments. The actual
delayed computation `C` remains distinct from its returned identity `W`. No later
fixture Call of `W`, successful-body hypothesis, or smaller challenge domain is
introduced by this result or this review.

## Frozen targets and integrity

| Target | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/NativeDictionaryDenotation.lean` | `d44a78f08970a09ca4c3e99a1d8dea846286a299d1a2bc91ec3b5e0eabea9070` |
| `notes/theory/2026-10-26-native-dictionary-denotation.md` | `c72586360b9c6a98c99093c0e239f73f49c0103f2d442f92cd492e1d871d7b3c` |
| `tasks/agent-loop/inbox/20261026-native-dictionary-denotation-r4.md` | `ea1e453832c096073069b221ceb238e01de1abc82e9fc2443d83d19a3d742f56` |

All 32 producer input paths match both their frozen `inputs/` copies and live
repository bytes. Both compiled outputs match the producer's frozen hashes. The
final isolated module and the two final per-call source snapshots match the exact
reviewed module. The census program matches its declared hash. All 22 receipt/log
manifest entries and all 11 receipt-to-log/source pairs match. The baseline commit
identity is supplied authority; this reviewer ran no Git command to restate it.

The earlier receiving trio remains byte-identical:

| Preserved input | Verified SHA-256 |
| --- | --- |
| `notes/theory/lean/YulangClosure/SourceFunctionMembership.lean` | `8d370ee57e486ae48607d1bab493ae5135f28bf8a5a7ff1b0ef240fc0247e424` |
| `notes/theory/2026-10-26-source-function-membership-construction.md` | `0ef65d4de31e7f2686217bfbdd547cd4f077325c45e80660a5791a7e31e9c2eb` |
| `tasks/agent-loop/inbox/20261026-source-function-membership-r4.md` | `9747fc7520a713c644ad33b219013043ab819f58460f63b390343a5c0960238f` |

## The theorem actually reviewed

The principal declaration is
`YulangClosure.NativeDictionaryDenotation.name_checked_dictionary_denotation`
at module lines 697–727. Its type retains arbitrary `Step`, `World`, `Site` and
`Binding`, one dictionary `World → List Step → Site → Option Binding`, and the
same `witness` and `site` on both sides.

Its independent structural premises are exactly:

1. `DefaultsValid words defaults`: each stored raw default has a word/context
   interpretation in the input word arena.
2. `substitution words subs value = some v`.
3. `substitution words subs current.substitution = some c`.
4. `context words current.context = some caller`.
5. `context words raw = some input`.
6. `instantiate.isSome = true → (defaults cell).isSome = true`.

For every `fuel`, `cell` and `instantiate`, the conclusion equates the Option-bind
lookup through the constructed `nameChecked` result with the lookup through

```text
resolve (defaultMeaning words defaults)
        (nameAction v c caller cell instantiate)
        fuel
        (action (nameAction v c caller cell instantiate) input).
```

Both lookup functions are the identical `dictionary witness · site`. The left
side interprets the same raw default map in the resulting word arena; the proof
derives its equality with the old interpretation using
`name_defaults_unchanged`. The final lookup may be `none`; there is no premise
that dictionary lookup, a selected body, default resolution, final-world
validation, or source checking succeeds. `World` is an arbitrary interpretation
parameter, not a constructed original `(nu,K,D,eta0,event)` telescope.

The raw construction is substantive. `applyDag_denotes` at lines 461–508 has
only a successful substitution-node interpretation and an input-context
interpretation as premises. It constructs **one** output arena/context pair,
proves that `applyDag` returns that pair, proves the exact ordered decoded
action in that pair, and simultaneously preserves every successfully interpreted
old word handle there. The Then proof transports the second child's replacement
interpretations through the first child's arena preservation. It neither assumes
an appropriate final pair nor chooses unrelated outputs for the two children.

The structural decoding hypotheses are real premises, not kernel axioms and not
original descriptor membership. In particular, native execution can skip an
ill-formed replacement in a nonmatching Assign, while `subAt` still requires that
replacement to decode. The frozen note explicitly excludes equivalence for that
malformed state. No all-source admission claim is inferred from these hypotheses.

## Runtime and source correspondence review

The entire delivered Lean module was inspected. The following comparisons use
the actual frozen Rust owners, not only the producer's prose table.

| Owner and proof surface | Review result |
| --- | --- |
| `dispatch.rs` lines 33–94; `wordAt`, `word`, `append`, `join`, `compose` | Optional handles denote the empty word/identity. Step appends its complete payload; Join is ordered concatenation. Fresh indices equal the prior arena size. Successful child interpretations are strictly backward, matching native edge guards. Old successful meanings survive extension; invalid future handles are not falsely promised to remain invalid. |
| `dispatch.rs` lines 103–141; `assignRaw`, `applyDag` | Assign matches the exact base, replaces the base and prefixes the replacement word. Nonmatch leaves the raw input/arena unchanged. Native Then pushes `[b,a]`; popping executes `a` before `b`, matching `action_append`, `then_denotes`, and the raw DAG induction. Repeated DAG sharing is retained rather than deduplicated. |
| `dispatch.rs` lines 143–159; `initializer`, `initialize_fresh`, `initializer_defaults_valid` | Defaults retain the raw parent context; inherited substitution is separate. Duplicate insertion mutates the map before returning an error, as represented by the mathematical initializer. This does not imply full error-state correspondence. |
| `dispatch.rs` lines 161–185; `name`, `nameChecked`, `name_denotes` | The instantiated branch checks default presence, appends the Name step to the raw caller context, creates Assign, then composes value/Assign/caller in that order. Caller substitution is not preapplied to the replacement. `ready` is exactly the entry guard. The uninstantiated branch composes value/caller without a fresh word or Assign. |
| Non-idempotence witnesses, module lines 607–627 | The concrete ordered `[1 := empty; 0 := 1]` witness distinguishes one application from two. `name_applies_caller_once` preserves the Name step. The explicit default self-cycle fails at every finite unfolding fuel. These are algebraic witnesses, not source counterexamples. |
| `dispatch.rs` lines 187–246; `resolve`, `dispatchMeaning` | Initial action precedes default resolution. Each default receives the same substitution, then its word prefixes the accumulated suffix. Step/Join flattening is left-to-right. `dispatchMeaning` is the mathematical interpreter; this review does not relabel it as a Lean verification of Rust's iterative loops or counter. |
| `machine.rs` lines 2596–2624 | Environment substitution is old then incoming; dispatch appends the exact step. `dictionary_names` membership chooses the instantiated Name branch. `dispatch_name` changes only the existing received packet's `dispatch` field. This code fact is not equality of complete worlds or a proof of the other receiving fields. |
| `machine.rs` lines 747–779 | FieldTail resolves the full word and exact site, uses that key in the fixed table, and appends Member for body entry. Missing lookup remains `UnsupportedFieldTail`. Forward uses the same environment. |
| `program.rs` lines 392–415 and 1242–1253 | All owner/occurrence information remains in each step/site. Definition/Local become Name; Operator/Member remain distinct. Conflicting members at a key are rejected. Entries point to registered member-body labels. This establishes the stated dispatch-index construction, not its whole typed evidence interpretation. |
| `program.rs` lines 806–818 | Group/Ascription forwarding is qualified by this bounded LocalSource owner's lack of applicable registered effect-upcast adapters. No general annotation erasure theorem is claimed. |

The arbitrary Lean `Step` can retain the entire native `(Kind, SourceRootId,
HirOccurrenceId)` payload. Neither source spelling, word length, kind alone nor
receiver type is used as a replacement key. Natural-number scope identities are
the mathematical representation of successful finite native indices; no overflow
or allocator theorem follows from that representation.

The original sources were read at their actual clauses:

- `notes/design/2026-10-08-contextual-function-membership-definition.md` §2
  preserves all independently admitted complete challenges, same actual
  decompositions and every observation/future development.
- `notes/theory/2026-10-08-call-semantic-input-realization.md` §2 and §§4.1–4.2
  retain the original fiber/assignment, actual current event, shared binding
  projection and hereditary certificate. Pure Return does not discharge latent
  Function obligations.
- `notes/design/2026-10-08-source-generalize-definition.md` §2 and
  `notes/theory/2026-10-08-source-generalize-definition-and-proof.md` §§3.3 and 6
  retain binding/provider identities and complete fixed dependencies. Genuine
  Specialize needs an actual source dictionary/template mechanism; installed
  monomorphic contracts retain Established/OneShot fields. Reinterpreting a
  retained execution is not rerunning its initializer.
- `docs/yulang-dot-selection-safety-ja.tex` lines 381–610 and 845–910 do contain
  whole-packet instantiation, the concrete typed nominal `Dict_R` record, shared
  captures, finite Hyp/Impl/Assoc evidence and M/R/F selected-code construction
  with direct argument/result adapters. Its opening says that the manuscript's
  paper proof is not independent/kernel certification, keeps corrected-machine
  correspondence separate, and does not prove that all compiler-selected results
  supply the required evidence. This review accepts the new note's source
  characterization without promoting that whole manuscript.

There is no generic finding that dictionary semantics are absent. The typed
`Dict_R` record and the runtime `(word,site) → Label` dispatch index are different
representations, and the exact bridge remains the construction listed below.

## Evidence, complete census and actual commands

No new Lean or Rust execution was needed for a concrete unresolved review risk.
**Reviewer Lean calls: 0 of 2 permitted.** The assignment explicitly allows reuse
of complete frozen evidence. The checker results below are the producer's actual
receipts, independently reconciled against the frozen files, rather than claimed
new reviewer executions.

Pinned executable:
`/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake`.
The final helper log records Lake `5.0.0-src+eb6cafb` / Lean `4.35.0` and Lean
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, x86_64 Release. The pin,
Lake file and empty dependency manifest match their frozen inputs.

The final helper receipt `10-checked-dictionary.json` executes the exact
repository `check_lean.py` with the isolated project, pinned `--lake`,
`--timeout 115`, the named module and all 37 explicit `--theorem` arguments.
Its exact command array remains in that receipt and is copied, together with
all 11 receipts, to this review's `integrity-result.json`. Its actual log records:

```text
lake --version
lake --no-cache env lean --version
lake --no-cache build +YulangClosure.NativeDictionaryDenotation
lake --no-cache env lean -j1 -M1024 --root=<owned audit directory> <owned audit file>
```

The executable is the pinned absolute path above; the exact generated audit paths
are retained in the producer's log. Final helper exit: 0; wall 4.991688 seconds;
peak aggregate sampled RSS 927268864 bytes. Final originating census command,
from the frozen isolated project, is exactly:

```sh
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake --no-cache env lean -j1 -M1024 AuditNativeDictionaryDenotation.lean
```

Final census exit: 0; wall 1.024539 seconds; peak aggregate sampled RSS 901685248
bytes. Both check the reviewed final module hash. Producer execution used the
reported normal authorized escalation path, single CPU/thread, owned TMPDIR,
`PYTHONDONTWRITEBYTECODE=1`, the 119-second outer/115-second helper bounds, and
the 1-GiB sampled aggregate cap. No resource termination is recorded.

The census code was inspected: it selects theorem constants by originating module
index, includes private/generated declarations, rejects project axiom declarations,
checks every required root, emits a full type and transitive axiom list for every
entry, and rejects dependencies outside its whitelist. The delivered module
imports only `Init`; source inspection finds no proof holes, project axioms,
unchecked native evaluation or kernel bypass. The normal `decide` witnesses are
not `native_decide`.

| Scope | Count | No axioms | Only `propext` | `propext`, `Quot.sound` |
| --- | ---: | ---: | ---: | ---: |
| Authored theorem roots | 37 | 7 | 13 | 17 |
| All originating theorem constants | 131 | 90 | 24 | 17 |

All 131 distinct begin/end blocks match the manifest, contain their complete type
and axiom line, and include every authored root. No ellipsis, `Classical.choice`,
project axiom, `sorryAx` or native-evaluation axiom occurs in this audit. The proof
is not described as axiom-free. The complete frozen audit is
`logs/11-final-originating-census.log`, SHA-256
`e301ada26982a93f8e6bd2ea877cf31c2a3648135522268ba03390a9ba845fb3`.

All 11 of the producer's 12 allowed checker calls remain accounted for, including
the four failed repairs `01-base`, `03-name`, `05-dictionary`, `07-raw-dag` and
their immutable source snapshots. Their actual errors are elaboration/normalization
repairs, not hidden counterexamples. Total producer checker wall time is
41.285092 seconds; largest call 11.064584 seconds.

The review's deterministic evidence command is exactly:

```sh
PYTHONDONTWRITEBYTECODE=1 TMPDIR=/workspace/scratch/f98087c7ac1a/dictionary-denotation-review-r4/tmp python3 /workspace/scratch/f98087c7ac1a/dictionary-denotation-review-r4/review_integrity.py
```

It exits 0 after reconciling 120 hash comparisons and the independent census
counts. Its first invocation exited 1 because the review parser incorrectly
required a leading `@` on every pretty-printed theorem name. Inspection showed
Lean omits that marker when unnecessary. The parser was corrected to accept the
two exact full-name forms; all name, block, axiom and hash checks remain. This
review-only parser repair is preserved in `integrity-parser-repair.json`; it was
not a proof failure and changed no producer file. Routine read-only `rg`, `cat`,
`sed` and `nl` inspections supplied the source comparisons above.

## Original-parent application and remaining owners

**What this removes:** once the original source packet is actually mapped to a
native dictionary interpretation, the checked equation supplies the identical
dictionary observation after the real ordered Name construction, retaining the
same raw defaults, dictionary, complete step/site information and supplied witness.
The raw DAG/Name algebra no longer needs to be assumed as an opaque law.

**First remaining source construction:** the primary's source/selected-use proof
lane must construct a map from one original shared `(nu,K,D,eta0,current event)`,
binding/reference, real specialization-or-alias event, and full member/role evidence
packet to the exact native instantiation word/site, registered body label, actual
captures and direct argument/result adaptation plan. Its equations must preserve
one whole instance across all fields/ports/captures, identify `dictionary_names`
with genuine source instantiation rather than monomorphic aliasing, and restrict
the selected body's source certificate to the same actual current event. The
source Specialize/body-template rules and `program.rs` selected-use/member-template
owners are the concrete seam. Equality of labels or the arbitrary `World`
parameter alone does not construct this map.

**Further unchanged source parents:** the primary/source proof lane still owns the
full descriptor/context/annotation/history interpretation, all `PhiW` fields,
original `P_F` phases and independent observations, `ValueMem_F†`, and `SourceT`.
The same source-scoped shared witness and whole inference/native parent obligations
remain OPEN. No source-qualified contradiction or counterexample was found.

**Runtime boundary:** the primary's runtime/native correspondence lane retains
any required proof connecting the mathematical interpreter to actual successful
Rust execution under its combined `32_768` counter and allocation limits, including
the relevant failure publication/mutation contract. `resolve` fuel counts default
unfoldings only. This is not a demand for unconditional full rollback, which the
governing inference principles do not require, nor a claim that algebraically
denotable inputs necessarily fit the runtime resource envelope.

## Ownership and stop receipt

The only repository write is this exact review handoff. All other reviewer writes
are under `/workspace/scratch/f98087c7ac1a/dictionary-denotation-review-r4/**`.
There were no Git operations, producer edits, Rust changes/tests, root imports,
shared-status changes, configuration/dependency writes, child agents, live checker
processes or approval requests. The isolated review evidence includes the integrity
script/result, parser-repair receipt, and extracted full key theorem types/axioms.

**WRITES STOPPED after freezing this handoff.** The exact cessation timestamp and
this handoff's final SHA-256 are recorded in the review scratch `STOPPED` and
`output-hashes.json`. The parent owns adjudication, integration, shared status,
any successor assignment and Git. Acceptance applies only to the target hashes
listed above; a subsequent producer change requires the applicable delta review.
