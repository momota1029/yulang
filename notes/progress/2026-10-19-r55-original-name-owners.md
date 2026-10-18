# R55 source-owner map: original direct-Name provider

Status: read-only source/native owner audit in R55; parent mapped-admission
premise OPEN 0→0. Contract `tasks/agent-loop/sprints/original-name-core-20261019-r55.md`,
revision 1, SHA-256 `4c292a24c7fba19c40587fcc2cb9374fdbff3dd7059533548e4e1be1420546d1`.
Baseline `a703e158c`. No code, tests, builds, parser/solver/runtime execution,
probe, measurement, or production change.

## Original-domain source entrance

The source-constructor shape to track is:

```text
my outer (q:[io] int) = {
  my forward (t:[io] int) = t;
  forward q
}
```

On the resolved source carrier, `q` is the current Computation formal of
`outer`; the whole argument of the forwarding call is its direct Name. The
nested `forward` is a one-parameter explicitly annotated Computation function,
and its body is the direct resolved Name of its own formal `t`. This is an
original-domain constructor candidate, unlike R51 `k forward`, R53
`loop forward`, or R54's higher-order `q t` discriminator. No parser,
preflight, complete ordinary solve, or runtime execution was run; the trace is
conditional on these exact resolved source constructors reaching source
execution. The parent fragment and its quantifiers are not narrowed to this
example.

## Producer-to-consumer path

| Stage | Current owner | Established source/native fact | Remaining limit |
| --- | --- | --- | --- |
| Formal registration | `candidate_source.rs:869–879, 956–1040, 1009–1021` | Original binder, annotation, Computation role, scope, and entry-effect endpoint are registered before its body actions. | This is source registration, not a received runtime entry or a `FreshUse` map. |
| Direct formal Name | `candidate_source.rs:1218–1230, 1661–1667`; `candidate_effect.rs:1437–1445` | A Name resolved to the registered Computation parameter emits `FormalNameEffect`; `candidate_formal_effect_equal` admits both physical directions `e_t<=e_n` and `e_n<=e_t`. | Repeated variable identity/equality does not say these bounds are present in a later copied graph. |
| Lambda result port | `candidate_source.rs:1666–1668`; `lib.rs:11323–11381` | Lambda admission supplies direct body effect `e_n<=e_R`; Computation omits slot 3. The original template chain follows from the emitted constraints. | The original template lemma is not the instance-relative mapped-bound premise. |
| Local publication and callee use | `candidate_source.rs:1090–1125, 1240–1253, 1668–1689`; `candidate_scheme.rs:1965–1985, 1995–2040` | Install publishes the live local root/boundary. The `forward` callee Name routes through ordinary Local capture and one `prepare_candidate_fresh_use`; the argument `q` remains a Parameter Name and emits its own registration fact. | No claim that every original-domain provider exposure is Local, or that every completed solve reaches this prefix. |
| Definition use | `candidate_source.rs:1228–1238, 1665–1687`; `lib.rs:16664–16884` | ModuleDef Names route through `Action::Module` and the actual incoming-route owner; open recursive uses are a separate path. | `DefinitionUse`/incoming FreshUse must be analyzed separately from Local capture; no global source-path enumeration is proved here. |
| Capture closure | `candidate_scheme.rs:755–790, 945–1005, 1054–1132, 1185–1292` | Capture canonicalizes representatives, traverses actual Function ports and stored bounds, and expands a row's adjacency only when `level>boundary && !non_generic`. | A shared-anchor stop and physical owner direction can omit a desired edge; local-template reachability is a separate owner premise. |
| FreshUse map | `candidate_scheme.rs:1496–1608, 1715–1755, 1860–1906` | One `canonical_rows` map produces images for captured local generic rows; Function endpoints and retained bounds consume that same map. | The code does not prove the original registration/Name/Lambda bounds are all in every relevant capture. A row map is not proof the mapped bounds were admitted. |
| Bound restoration | `candidate_scheme.rs:2153–2183`; `candidate_extrusion.rs:763–789` | The Local route restores each captured bound before linking the fresh root to its actual use. This is the right point to inspect physical mapped `BoundKey`s. | Restoration covers only captured graph bounds; missing capture cannot be repaired by the map itself. |
| Apply and signed copy | `shadow_apply.rs:1780–1923`; `lib.rs:12558–12683`; `candidate_extrusion.rs:21–258,330–340` | Actual demand comparison may trigger signed structural extrusion; each operation records signed parents/source links, then copies selected bounds and drains replay. | Provider closure coverage depends on actual entry sign, target, source event, and complete parent group. No whole-constructor induction is supplied by local code mechanics. |
| Merge and later replay | `candidate_intrusion.rs:308–386,568–713`; `candidate_extrusion.rs:867–969` | Only qualified event/source groups merge. Merge appends both stored sides, lowers level by min, ORs nongeneric metadata, redirects representatives and replays lowers; ordinary admission chooses a physical owner at that admission. | Neither quotient preservation nor the original maximum-level insertion rule proves that original provider bounds survive all later aliases, parent merges, or recaptures. |
| Failure/rollback | `lib.rs:9056–9064, 9278–9350, 9435–9480`; `candidate_intrusion.rs:201–203` | Incoming Local-route failure runs its transaction rollback; a failed candidate inference returns no successful candidate. | This audit does not prove an end-to-end source/evaluator recovery theorem or same-session replay of failed source actions. Failure cannot be counted as a successful mapped instance. |

## Exact unresolved owner judgment and code-slice disposition

The first general missing judgment is an induction on *original-domain* source
events showing that every later qualifying extrusion/merge/replay either
keeps the same provider's `e_t/e_n/e_R` rows together in the actual capture,
or creates a physical alternate route between the images under that use's one
FreshUse map. A direct-Name provider's local source-reference component alone
does not settle this: earlier qualified event source sets can survive replay,
and an ancestor group can merge rows reached through a different signed
entrance. The required record is the actual event/source set, signed
`BoundKey`, representative and level history, followed by the next real
Capture/FreshUse and bound restoration. Sol's independent attack is checking
this specific noninterference assumption.

Sol's adversarial lane also identified this original-domain recursion scaffold
for the owner trace (not a counterexample as yet):

```text
my outer (q:[io] int) = {
  my forward (t:[io] int) = t;
  my loop (x:[io] int) = {
    my a = forward x;
    my z = loop x;
    z
  };
  loop q
}
```

Each shown call passes its current Computation formal by direct Name; the
single local `loop` self-recursion uses the approved active-root seam. Its
qualified event/group must be traced against the separate `forward` provider's
same-use rows. `forward`'s own sink-shaped source SCC does not by itself exclude
an ancestor group that reaches its copied bounds. No native execution or
missing `BoundKey` is claimed here.

The instance correspondence `mu` must also stay partial and owner-derived.
For each endpoint needed by the parent premise, identify its actual image as a
captured local row in the one FreshUse table, an existing shared row retained
by identity, or a representative reached by a real merge. An endpoint absent
from capture has no FreshUse image merely because a canonical map exists.
The common bound correspondence must cover the required `e_t`, `e_n`, `e_R`
edges; it cannot be totalized by notation.

No safe code slice is identified. The gap is an original-domain proof over
source generation and existing consumers; this packet grants source inspection
only. R51–R53 source examples that pass a callable as an argument and R54's
higher-order discriminator are not substituted for a parent instance. Their
owner lemmas may be reused only where the original source event and operation
premises match. Parent quantifiers, source domain, semantics, expected outputs
and Simple-sub A/B remain unchanged. R50 remains NOT ADOPTED.
