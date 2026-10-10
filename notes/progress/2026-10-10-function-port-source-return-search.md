# Nested Function checking ports: exact copy exposure search

Status: frozen, unreviewed research-only bounded source characterization and
conditional constructor derivation. No ordinary-source counterexample, global
impossibility theorem, defect, restoration-R closure, or implementation authority.
Baseline supplied by primary: `06f91e94fb86c369d020457c66953c42fd7bebc3`.
Producer/lease: `function_port_source_search`; this note only.

## Objective, authority, and result

Search the nested Function route left open by
`2026-10-10-hir-owner-scc-return-path.md`: can ordinary source expose the **exact
positive incidence copy C** of a negative Allowance owner S in a Function port,
then produce `C -> ... -> S` without qualifying the original tail pair?
The method is static inspection of the paired formal constructor, whole/local
annotation constructor, Lambda domain owner, structural extrusion, actual SCC
edge builder, and the normal sequential source scheduler. The main constructive
obligation remains assigned to the primary's proof lane.

Governing authority is contextual attachment/admission design §§3.1–5.
Occurrence-local attachment sets and member ordinals, composed annotation
polarity, scoped variable identities, level-selected orientation, actual
parent/copy provenance, and contextual transfer retain their selected meanings.
Concrete composed-negative annotations remain guarded. No source restriction,
changed annotation meaning, handler interpretation, or acceleration assumption
is introduced. Research-lab, design-authority, git-concurrency,
agent-orchestration, and the yulang-proofs skill were read.

**No authentic successful source prefix was established.** Nested Functions
do expose negative checking S structurally, but the initial constructor gives
S a negative term. If that term is copied structurally, it selects
`Key(S,Negative,t)`, while incoming-tail extrusion selects
`Key(S,Positive,t)`. These are distinct operation-local maps. Merely finding S
inside a nested Function therefore does not expose its positive incidence C.
The root-only note's absence of any structural exposure can be sharpened here
to an exact **polarity and copy identity** obstruction.

This excludes only direct construction/structural copying of the fresh
checking port under the hypotheses below. A positive paired port P can later
become an Allowance owner through admitted checks. If that occurs, its positive
structural occurrence and incoming-incidence visit select the same positive
map, and the initial obstruction does not apply. Establishing that later
registration from the normal scheduler is the precise remaining seam; it is
not ruled out. Source reachability beyond this seam and both SCC tests remain
open.

## Allocation identities and source-owned schedule

The following real authored syntax occurs in `candidate_effect.rs:1706`:

```yulang
act io
my bridge (consume:(int -> [io, 'e] ()) -> ()) = consume
```

It is a locator for the constructors, **not a new executed witness**. This
worker did not parse/lower/run it. In particular the unit test invokes a
selected FormalAnnotation directly after starting a graph; it does not execute
the normal complete source schedule. The two-position sibling at `:1768`
explicitly sets the parameter level to 2, so its level/capture assertions
cannot establish ordinary-source scheduling.

For the first syntax, the normal planner puts FormalAnnotation before the body
visit (`candidate_source.rs:241–262`), and the dispatcher calls its constructor
at `:553`. For an actual initialized source run, parameter levels come from
`initialize_candidate_source_levels` (`:507–518`); the normal initial source
level is 1 (`:229`). No numeric live row IDs or completed admissions are claimed
here. The symbolic identities name exact allocation sites:

| Identity/action | Owning producer |
| --- | --- |
| `V_consume` | Parameter endpoint; its level determines formal construction (`candidate_effect.rs:941–956`). |
| `T_e` | One scoped `annotation_effects[(scope,"e")]` entry, allocated at first occurrence and reused (`:844–864`). |
| `v_e` | One paired view for the concrete-plus-tail row at the nested callback result position (`:924–930,1391–1416`). |
| `P_e` | Fresh positive port with physical `P_e + Support(v_e[T_e])` (`:1420–1433`). |
| `S_e` | Separate fresh negative port with physical `S_e - Allowance(v_e[T_e])`, made by the negative call to the same constructor. Reusing the view does not reuse this port row. |
| slot 43 | Positive formal Function tree `<: V_consume` (`:965–966`). |
| slot 44 | `V_consume <: negative formal Function tree` (`:969–970`). The negative tree is retained as `formal_domains[parameter]` (`:971`). |
| body Name | Uses the Parameter endpoint; evaluation receives only ordinary pure facts (`candidate_source.rs:184–191,338–348`). |
| Lambda domain | `admit_lambda_fact` reads that exact retained negative tree, rather than deriving a domain from the exposed positive tree (`lib.rs:11130–11134`). Its body result is the Parameter row (`:11142–11150`). |

Formal construction starts at composed-negative variance. At the outer
Function's argument the variance reverses to positive; the inner callback
result therefore takes the mixed covariant port branch. In the positive
formal tree the callback is a negative Function whose result port is S_e;
in the negative formal tree it is a positive Function whose result port is P_e
(`candidate_formal_pair`, `:908–916`). Both are real structural exposures,
with distinct port identities and polarities.

The Lambda then places the negative formal tree in its argument, so P_e can
be at a positive total position after two argument reversals. The returned
Parameter's positive formal tree instead contains S_e at negative polarity.
Finding the former P_e does not establish that the recorded original owner
was S_e. Finding the latter S_e does not make its positive copy C_e the
structural result. Scope reuse identifies T_e only, and cannot repair either
identity mismatch.

## Conditional derivation: direct structural copying cannot select C_e

Hypotheses: one successful constructor/extrusion prefix in a valid candidate
session; valid row/view indices and representative forests; no rollback,
external interleaving, or intervening row merge; S_e and T_e both above target
t when the indicated visits occur; S_e is the fresh checking port just
constructed, with no separate positive term occurrence introduced by later
constraints or reconstruction. Only direct traversal of the identified
annotation Function tree is being characterized. Any additional bound walk
must be identified separately. Ports P_e/S_e have not been equated.

1. Whole/local/ascription signature construction chooses the requested term
   polarity and reverses it at Function arguments; results preserve it
   (`candidate_effect.rs:1256–1301`). A newly allocated Allowance checking
   port is returned by the **negative** branch (`:1420–1433`). Its positive
   mate is a fresh P_e with Support, not the same row. Paired formal
   construction preserves this positive/negative distinction recursively
   (`:908–935`). Omitted and singleton-symbolic formal ports share a row pair,
   but this branch introduces no mixed Allowance owner at that occurrence.
2. Structural extrusion keys are `(canonical endpoint, polarity, target)`
   (`candidate_extrusion.rs:5`). Function argument ports reverse the traversal
   polarity and result ports preserve it (`:209–244`). The copied term uses
   the corresponding child key (`:329–351`). Thus a structurally visited
   negative term S_e maps through `Key(S_e,Negative,t)` to D_e.
3. A positive visit of T_e traverses its registered incoming Allowances and
   visits their owner with **positive** polarity (`:163–179`). It creates C_e
   through `Key(S_e,Positive,t)` and inserts its remapped negative Allowance
   (`:293–305`). Separate keys yield separate fresh rows D_e and C_e when
   both are needed above t. The returned structural Function reads D_e for
   the negative checking position; it does not read C_e because the rows
   share S_e, a view, target, or creation provenance.
4. The operation adds the one-sided source links by inserting a bound on the
   original owner (`:140`). In the SCC adjacency both polarities therefore
   give **S_e -> copy**, not `copy -> S_e`. In particular a negative copy D_e
   supplies no automatic physical return `D_e -> S_e`. Reading its logical
   inequality in reverse as graph adjacency would invent the desired edge.
5. The SCC builder follows both physical bound sides from owner to item,
   views to their tail, and Function constructors to their actual ports
   (`candidate_intrusion.rs:382–474`). Creation provenance and capture
   incidence are not extra SCC edges (`:482–493`). Making D_e visible in the
   copied negative position therefore does not provide the missing return
   from C_e to original S_e.

This is an operation/constructor-local conditional derivation for arbitrary
finite nested Function depth within the admitted constructor envelope. It is
not an induction over all successful source constraint histories. It does not
establish that later aliasing, constraints, bound transport, or a qualifying
merge can never create a positive occurrence of the exact canonical owner.

## Alternate exposed owners: the unproved source registration seam

The initial port distinction must not be promoted to “every Allowance owner
is negative.” `candidate_apply_effect(P,Allowance(w[T]))` directly inserts
that upper on the true P receiver, regardless of P's annotation allocation
role (`candidate_extrusion.rs:726–751`). Insertion registers the real
incoming-incidence record (`candidate_effect.rs:426–433`). There is no
permanent ownership tag that would prevent such a P from also having a
positive structural occurrence.

A second actual row comparison can produce that registration through opposite
replay. Conditionally, if P is canonically older than checking S and
`P <: S` is admitted while `S - Allowance(w[T])` exists, the selected positive
lower is put on S and replay emits `P <: Allowance(w[T])`. At equal levels
the direct row comparison instead stores an upper S on P; one must trace its
actual replays, not assume transitive physical upper installation. The Value
owner can first extrude the written negative Function demand to its own older
level (`lib.rs:11958–11973`), so merely choosing a syntactically deeper
annotation does not establish the required older/younger effect-port relation.

If such an exposed positive P really acquires an Allowance, positive structural
copying and the corresponding incidence visit can select **the same**
`Key(P,Positive,t)`, exposing C_P. This is a viable candidate premise and a
different method from another isolated tail-only probe. The present static
inspection did not establish a complete ordinary-source prefix for it, its
actual levels, a later `C_P -> ... -> P`, or tail nonqualification.

The formal constructor test at `candidate_effect.rs:1757–1763` asserts two
physical Allowance incidence owners after its manual constructor admissions,
including a port with Support. Its two-position sibling similarly asserts
four owners (`:1781–1787`). These assertions flag the alternative for further
investigation; this worker neither ran those tests nor promoted their
hand-driven initialization or manipulated level schedule to source evidence.
The positive-extrusion regression at `:2087` directly allocates checking/tail
rows and calls extrusion, so it also cannot fill the required source prefix.

Finally, a positive P whose only tail-bearing Support uses the same original
tail as the captured Allowance deserves separate caution: replay of that
Support against a later checking boundary exposes the copied tail. A return
through that tail repeats the previous note's conditional closure of both
recorded pairs. A route relying on a different Allowance tail must identify
the exact occurrence, scope and remapped views; different spellings are not
an identity certificate. No new claim about complete replay is made here.

## Checks, coverage, resources, and stop condition

Commands were bounded `cat`, `sed -n`, `rg`, `rg --files`, and `sha256sum`,
plus creation of this leased note with apply_patch. Static coverage is the
listed constructor, planner, Lambda-domain, copy-key, bound-admission, and SCC
seams. No source-program enumeration or live row trace ran. Some combined
captures truncated; the code used above was subsequently read in narrow
slices. A listing located existing binaries, but none was executed: a public
CLI result would not expose these private live row/map identities.

No executable oracle or independent language oracle was used. The derivation
shares the inspected compiler's constructor and transition assumptions;
therefore it cannot prove those assumptions from an external model. Seeds,
ranges, mutations, executable samples, tests/builds: none. No helper, cfg(test)
change, compiler edit, formatting, Git command/mutation, delegation, or shared
record edit. Zero heavyweight processes; only short shell read processes.
CPU, peak RSS and total wall time were not measured. The assignment specified
source/static work and a witness-or-exact-obstacle stop condition, with no
numeric wall/RAM allowance.

Stop condition: the initial nested checking-port route has a precise
copy-polarity identity obstacle. The uncovered alternative is registration on
an already positive exposed row under the real scheduler, with actual
post-extrusion levels. No third equivalent tail-only or artificial graph probe
was started. R stays open; a defect would additionally need the original
within-restore mutation, exact missed fiber pair and failure of all later
replay/diagnostic rescue.

Unverified: parse/lower success in this run, complete normal action execution,
numeric row/view IDs, late positive-owner registration, actual parent records
and both SCC memberships, recursive/provider schedules, intervening
canonical merges, rollback/retry, and whole-use diagnostic coverage. This
producer supplies no independent review of its own result.

Recommended next action: trace one complete ordinary-source schedule in which
an **already positive exposed Function effect row** receives a mixed Allowance
through actual admission/replay; identify its exact source action, levels and
views before spending effort on the C return or restoration mutation.

## Dependencies and commit packet

Initial inspected dependency hashes:

```text
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0  crates/yu-solver/src/candidate_source.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  crates/yu-solver/src/candidate_effect.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  crates/yu-solver/src/candidate_extrusion.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11  crates/yu-solver/src/candidate_scheme.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  crates/yu-solver/src/lib.rs
6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6  crates/yu-solver/src/shadow_apply.rs
9d8a717407c711a6ffbc8734e5c4bceb609893ff691a8778737177da2c96cc0c  crates/yu-solver/src/candidate_context.rs
6e8a41bc27e0570c916cf49fa4e4a916b6bb6059ad8b0c32627a2d33a0cfbf93  notes/progress/2026-10-10-positive-tail-source-composition-proof.md
4243139aa2d00cffb5fe1e767786e391a88bfa8b9aa64f07c21a59c380ba5922  notes/progress/2026-10-10-hir-owner-scc-return-path.md
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
```

Commit packet: exact leased/changed path
`notes/progress/2026-10-10-function-port-source-return-search.md`; baseline
`06f91e94fb86c369d020457c66953c42fd7bebc3`. No dependency changed by this
worker. Final recheck found concurrent `candidate_context.rs` movement from
`9d8a717407c711a6ffbc8734e5c4bceb609893ff691a8778737177da2c96cc0c` to
`3b219b51ed8aba6ffc85675fd1d500b901a6f63b31325a85a586d688eee3515a`;
the other ten hashes remained unchanged. The closed-Allowance source selector
and actual-receiver registration consumer were narrowly reread and remain at
`:1607–1620,1838–1902`. This is not full-delta certification; the core
constructor/copy-key argument uses the unchanged source files. Baseline-blob
comparison and complete delta validation are left to the primary.
Review status: frozen, unreviewed, research-only bounded
characterization and conditional constructor derivation. Checks already run:
static source inspection and dependency hashing only; no tests/builds/probes.
Proposed one-line checkpoint:
`research: isolate nested Function copy-polarity exposure obstacle`.
Shared-record deltas intentionally left for primary/curator: record the
checking-port positive-incidence/negative-structural map distinction, preserve
the later positive-owner registration alternative, and retain R/source-prefix,
both SCC tests, restore-loop mutation and whole-use rescue as open. No shared
task, index, authority, theory, manifest, lockfile, or question bundle changed.
