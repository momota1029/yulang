# Compose scope release: source supplier falsification

Status: frozen, independently reviewed research characterization; no parent theorem or implementation gate closes.
Review: `spec_auditor` (`review_hygiene_block_clarification`) checked the pinned constructors and transport sites; no findings.
Baseline: `261605657dbcd391d87b7eaa2c68b2a59349fa47`, branch assigned as `research/simple-sub-intrusion`.
Method: bounded static source derivation, complementary to the constructive proof lane.
Lease: this file only. No compiler edits, tests, builds, executable probes, delegation or Git mutations.

## Authority and exact candidate premise

Governing sources are the October 15 compose decision, “Scope of the operation”;
the directional addendum §2; annotation hygiene §1.1; and top-level inference
principles §§1–3. Release removes one selected scope and preserves contributions,
attribution and other scopes. A protected inferred variable's original Function
upper use protects its output occurrence; existing provider lower provenance
does not gain that protection backwards.

The candidate finite algebra communicated by the primary uses immutable input
tags, `StampInput(u)`, `ProtectBody(F,u)` conditional on absence of tag `u`, and
`Release(E)` deleting exactly scope `E`. This note does not refute that algebra.
It falsifies the narrower supplier premise:

> The baseline's `DirectionalIntroduction` records enumerate every source
> upper exposure that needs the omitted formal's protection scope.

The conclusion is a source-code coverage fact, conditional only on using that
particular record family as the complete supplier. It is not an executed
compiler counterexample or an independently reviewed hygiene theorem.

## Small alias witness and derivation

The distinguishing source forms are:

```yu
my direct cb = cb()

my aliased cb = {
    my alias = cb
    alias()
}
```

These snippets were not parsed or executed in this packet. The derivation is
over their ordinary `LocalSource` forms: an unannotated Lambda parameter,
`Name(Parameter(cb))`, a local binding initialized by that Name, and
`Apply(Name(Local(alias)), Unit)`. Local blocks/bindings/names and these Apply
forms have explicit owning native constructors at the pinned revision; no
invented transition semantics is needed to establish the record omission.

1. `candidate_source.rs:388` retains `OmittedFormal` for each unannotated
   Lambda parameter, so both examples retain the `cb` omission witness.
2. `candidate_source.rs:323` initializes `formal_names` to `None`. Only
   `Name(Parameter(...))` creates a `FormalNameInput` at lines 327–334.
3. The direct Apply's callee is that parameter Name. Its
   `ApplySourceInput.formal_name` is therefore `Some`, by line 618.
4. The alias initializer is another parameter Name, but its later callee is
   `Name(Local(alias))`. Its table entry stays `None`: the only assignments
   besides parameter Names propagate through Ascription, Group and Block's
   final expression at lines 624, 654 and 678. No assignment copies a binding
   initializer's formal witness to subsequent `Name(Local(...))` occurrences.
5. This alias still takes the ordinary native route. The local initializer
   installs a `LocalScheme` rooted at the parameter's Value row
   (`candidate_source.rs:492`; `candidate_scheme.rs:1348–1367`). The local Name
   schedules `Action::Local` (`candidate_source.rs:597`), which uses the
   existing captured-graph/fresh-use path. Alias lookup does not produce a
   new omitted formal or invoke `Work::Visit(Lambda)` for that callee.
6. `shadow_apply.rs:1500–1521` constructs `DirectionalIntroduction` exclusively
   inside `if let Some(name_index) = source_call.formal_name`. Therefore the
   alias Apply has `introduction = None`, while the direct Apply has the
   omission-backed introduction, assuming both native constructions complete.

The callee's value-flow ancestry still originates at the protected inferred
`cb`. A collector treating the missing alias record as evidence of no
protection would impose a lexical distinction at the local-name boundary.
The baseline public accessor already documents the correct limitation:
`candidate_call.rs:254–256` says `None` means no authenticated route in this
carrier, not language-wide absence of protection.

This example minimizes the uncovered source seam to one local alias and one
Apply. A Catch or concrete effect declaration is unnecessary to distinguish
the constructor records. Adding the selected unannotated relay Catch would
make the missing scope observable only once actual hygiene consumption exists;
that observation was not executed here.

## Exact owning requirement for the candidate

Before treating source-introduction tags/scopes as complete, retain the
omitted-formal seed through the ordinary Value/local-scheme transport to its
actual Function upper exposure. The supplier must retain original seed,
actual exposure demand, original checking occurrence and fresh-use identity
as separate facts. Alias resolution is not permission to classify an external
known provider as a newly omitted formal.

The existing owner seams are `install_candidate_local_term`,
`prepare_candidate_fresh_use`, `begin_candidate_fresh_bound`, and the native
Apply demand constructor. The requirement is to connect these existing
construction facts; this note does not select a traversal or authorize a
production representation. The current Function-entry/body distinction at
`lib.rs:11254` remains necessary independently of this alias omission.

Fresh-use cannot be reconstructed from row equality: at
`candidate_scheme.rs:1012` every fresh use gets `context_use`, while lines
1047–1055 deliberately retain nongeneric/captured rows. Consequently two
fresh uses can share an endpoint but have distinct transport origins.
`begin_candidate_fresh_bound` explicitly records that distinction at lines
1282–1298. Any new stamp/scope rename must preserve it even for a shared row.
This is an owning transport requirement, not proof that every repeated use
must introduce a semantically independent scope.

## Coverage, independence and limits

All source reads used `git show 261605657:<path>` after initial locator reads.
No checker, reference interpreter, random seeds, finite enumeration, mutation
run or runtime oracle was used. Therefore there is no oracle-independence
claim: the record omission follows directly from table initialization and the
exhaustive assignments to that table in the pinned source. The accepted design
supplies the protection policy; current implementation does not supply its
own semantic authority.

The same baseline was inspected for entry/body construction, Function AE/RE
comparison and FreshUse. No counterexample to the immutable-tag algebra was
established. In particular, an entry contribution cycling through a recursive
provider's body remains entry-derived; merely observing that cycle does not
justify claiming it needs a new body protection. Computation-role annotated
arguments, late-lower replay completeness, recursive scope reuse, overlapping
release scopes and all-source tag authenticity remain unverified here.

No tests, builds or measurements ran. Static commands were `git show`,
`git grep`, `rg`, `git ls-tree`, `git status --short` and this leased-file write.
Process use was short read-only shell commands; zero Cargo or heavyweight
processes. CPU/RAM peaks and exact wall duration were not measured; packet
wall budget was approximately ten minutes.

## Frozen dependency snapshot and handoff

Pinned Git blob hashes:

| Path | Blob |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `f4271fffd07a7035e41f1885c63b0f78dbd6dbe1` |
| `crates/yu-solver/src/shadow_apply.rs` | `5062ddf457158ba1f8c7caa2cab57d21bdb324ee` |
| `crates/yu-solver/src/candidate_scheme.rs` | `cb460cb19bfe1bc7c4b5a660e8e5cbb17b4d1f8c` |
| `crates/yu-solver/src/candidate_context.rs` | `7c69b87365e9f11676b8fd6357b7dc4b0d507ece` |
| `crates/yu-solver/src/lib.rs` | `7f40fc4e1aa74720ef857134412f08d3b40e633a` |

Concurrent worktree changes were observed in `candidate_source.rs` and
`lib.rs`; they were neither inspected as dependencies nor modified. Claims
above are pinned-baseline claims. The primary must assess any replacement
supplier in its integration delta.

Recommended next action: make the alias pair an explicit constructor-coverage
obligation for the implementation/proof handoff, and establish its retained
seed-to-exposure transport before claiming a source-complete tag supplier.

Commit packet: exact leased path
`notes/progress/2026-10-15-compose-release-source-falsifier.md`; baseline
`261605657dbcd391d87b7eaa2c68b2a59349fa47`; no dependency changes made by this
worker, concurrent source dependencies above require primary revalidation;
review status unreviewed research-only; checks are pinned source inspection
only; proposed message `research: identify omitted-formal alias exposure gap`.
Shared-record delta intentionally left to primary/curator: record this
specific supplier gap under compose source correspondence without changing
semantic authority or closing the parent hygiene/proof gate.
