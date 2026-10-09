# Upper self: an outer consumer and a retained local root

Date: 2026-10-10
Status: frozen, unreviewed research; bounded source-owner derivation
Primary baseline: `4958aa8d434bb0f2168ffd42f5d21aa2d0316d38`
Local dependency pin: `3641e6ff4534e2b18b4bb9c110b1ccb4458267b8`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Method: owning-source construction trace; no compiler or checker execution
Production authority: none

## Objective and result class

Attack the missing original-row/root premise in the reviewed
[upper-self observer](2026-10-10-upper-self-filter-observer.md) and
[review](2026-10-10-upper-self-filter-observer-review.md): can one later
scheme expose deeper original Effect row T and an outer negative-extrusion copy
C, with C anchored and T fresh?

**Novel bounded derivation:** an outer bare consumer `h`, applied to a deeper
higher-order annotated formal `a`, forces negative extrusion of the nested
callback's Effect coordinate. The enclosing local lambda's retained negative
formal domain still contains that original coordinate. Its later local scheme
therefore has a construction-directed route to both T and C; exposure is not
an assumed inverse parent edge. A later Name in a deeper initializer supplies
the required fresh/anchor level partition.

This establishes the row/root incidence for the current paired **omitted-row**
constructor, conditional on the displayed LocalSource shape and successful
owner operations. Extending that incidence to explicit contextual formals,
and the keep/drop filter difference, is a **conditional theorem**, with the
exact unfinished constructor and payload premises below. This is not an
admitted source counterexample, a runtime defect, a complete hygiene result,
or permission to reject explicit annotations.

Governing authority: annotation-effect-hygiene-integration §§1,4,6;
concrete-effect-annotation-implementation opening policy and “Annotation
checking and publication owner”; paired-function-formal-construction-gate
“Constructor and dependency replacement” and “Rejected realization and source
limits”; paired-function-formal-integration “Actual constructor and consumer”.
The selected polarity meaning and corrected returned `int ->` callback target
remain unchanged. That callback target is not exercised here. Research-lab,
design-authority and git-concurrency were read in full.

## Source shape and explicit premises

The following successor-shaped text is an unexecuted source locator:

```yulang
act io
my bridge h opaque = {
  my f (a: (int -> [io; 'e] int) -> int) (g: (int -> [; 'e] int) -> int) = {
    my ignored = h a;
    1
  };
  my later = {
    my empty (k: int -> [] int) = 1;
    f opaque empty
  };
  later
}
```

Parsing, nominal lookup and diagnostics were not executed.
`act io` is the successor declaration form; it is not identified with the
historical Oracle fixture's `type io` producer.

Current explicit-formal rejection is an unfinished gate at
`candidate_source.rs:77–81` and `candidate_effect.rs:845–846`, not a selected
source restriction or an exclusion proof. The witness needs this gate opened
by the authentic constructor, not bypassed by fabricated solver input.

Premises for the contextual extension are:

1. The authentic paired formal constructor preserves the current Function
   polarity and source levels, resolves io, and shares the named Effect tail
   `'e` between a and g in f's actual local binding scope. Write this T at level
   2. For a's nested callback, its positive/negative interfaces have the
   retained symbolic coordinate underneath the original attachment/filter.
   Oracle's constructor supplies this topology; its exact successor contextual
   realization is unfinished. No rigid value/effect identification is assumed.
2. Paired replay offers the normalized self comparison `T <: T @ P`, where
   `P = PUSH_i[{io}]`, after the original `{io}` check/registration. The keep
   alternative retains it **only as** `U_T(T,P)`; drop omits that upper. Both
   alternatives retain the original annotation and its other structure.
3. Negative extrusion follows the actual underlying negative row T, installs
   `L_T(C,id)`, and preserves the needed occurrence/attachment structure.
   The contextual representation neither anchors T prematurely nor discards
   its root traversal. Capture/freshening preserve this structure and bound
   sides, map T to T', keep C anchored, and restore P with its original authority.
4. Ordinary restore/replay compares the opposite bounds and stores contextual
   `C <: T' @ P` by the current level rule. Consumed Empty filters check current
   and future positive lowers by the reviewed Oracle-style rule. No contextual
   memo/subsumption rule suppresses this comparison.
5. The finite continuation reaches the named observation without resource
   failure, earlier contradiction or rollback. C has no unrelated concrete or
   contextual positive lower that already makes drop fail. Parent equality
   does not first identify C and T or lower T to the anchor level.

Premises 1–4 contain unfinished implementation/correspondence work, not new
language decisions. In particular, the declaration's immutable annotation
support is not an emitted io contribution or a grant for other occurrences.

## Derivation from the actual owners

All successor line locators in this section use the local dependency pin.

### 1. A real source caller creates the outer copy

The top source starts at level 1. Lambda bodies retain that level. Each Block
initializer increments it; install uses the enclosing boundary
(`candidate_source.rs:193,209–248`). Thus h and opaque are level 1; f's lambdas
and a/g are level 2; the ignored initializer is level 3. The deeper initializer
does not change the referenced a parameter's level.

Local formals retain their annotations and actual local owner
(`module/local_source.rs:661–699`); `candidate_source.rs:140–144,215–223`
uses f's `AnnotationScope::Local`. With effect rows erased from the annotations,
`candidate_formal_pair:854–863` constructs the nested Function's shared ordinary
result-Effect row q at level 2, its positive and negative interfaces, and a's
positive and negative interfaces. The body row A receives the positive
interface and the negative domain is retained separately (:868–898).

`h a` produces the actual Apply demand `Fn(A+, ..., result-)` against h's
level-1 row (`shadow_apply.rs:1327–1358`). The row/structured-upper owner invokes
negative extrusion to h's level (`lib.rs:11853–11864`). Its traversal is:

```text
application demand negative
  -> argument A positive
  -> A's positive Function lower
  -> nested callback argument negative
  -> nested callback result Effect q negative
```

Function argument reverses polarity; result Effect preserves it
(`candidate_extrusion.rs:209–233`). Positive A traversal copies its selected
positive lower, not the separately retained negative interface. As q is deeper
than 1, the negative row visit allocates C at 1, records its genuine parent,
and directly inserts `L_q(C,id)` (:89–122). This conclusion uses a source Apply
caller and the actual formal lower. It does not posit a free extrusion event.
Under premises 1–3, replace q by the explicit underlying T and obtain
`L_T(C,id)` beside the kept `U_T(T,P)`. Insertion alone does not replay them.

### 2. The installed lambda still exposes original T

When f's a lambda finishes, `admit_lambda_fact` consumes the retained negative
domain N_a (`lib.rs:11109–11114`). N_a's callback argument is the callback's
**positive** interface. Its Effect coordinate is original q/T, not C.
The lambda lower is admitted to f's own level-2 root (:11173–11193).
Positive extrusion at target 2 leaves level-2 coordinates unchanged
(`candidate_extrusion.rs:89–92`). The inner g lambda finishes first; the outer
a lambda retains that g lambda in its result and N_a directly in its domain.
The h call rewrote h's demand/copy; it did not
replace f's retained formal-domain association.

`install_candidate_local` records f's original initializer root and boundary 1
without replacing that root with an escaping copy
(`candidate_scheme.rs:917–925`). At the later f Name, capture starts at that
live original root (:937–953,528–555), traverses the original lambda and its
negative N_a domain (:337–387), and reaches original T. T is local because
`2 > 1` (:200). Its row expansion retains **both** bound sides (:463–504),
including `L_T(C,id)` and the conditional self upper. It interns C, classified
as an anchor because `1 <= 1`; expansion stops at its older identity (:418).

Hence the captured graph contains original T and its lower C by the actual
lambda/domain/bound route. No inverse parent-metadata edge is used. The
source owner's explicit scope rule permits the ordinary omitted-row analogue;
authentic contextual traversal remains premise 3.

### 3. Later use supplies the strict level partition

The later initializer's Block runs at level 2, so its f Name has use level 2.
Freshening maps T to fresh T' at 2 and keeps C at 1
(`candidate_scheme.rs:737–749`). The same map is used throughout the captured
graph. Restore preserves owner side and compares opposite bounds
(:841–864; `candidate_extrusion.rs:557–591`). The keep comparison is:

```text
L_T'(C,id) + U_T'(T',P) -> C <: T' @ P
level(C)=1 < level(T')=2 -> L_T'(C,P)
```

The strict comparison uses `candidate_extrusion.rs:679–685`. Drop restores
only the identity-weighted C lower. This is the previously missing anchored
partition, now supplied by the source initializer and install/use owners.

### 4. A separate symbolic occurrence supplies Empty

The later call's first argument opaque is a bare outer parameter with no
positive Function producer lower. Its comparison can retain a's domain demand;
it does not compare a's attached callback directly with an Empty callback.
The second actual argument empty has a negative callback domain from its
formal `k:int -> [] int`. f's g domain has a positive callback with shared
symbolic T' and **no i PUSH**. Two ordinary Function argument reversals give:

```text
empty+ <: N_g(T')
  -> callback_g+(T', no i PUSH) <: callback_empty-
  -> T'+ <: Filter(U-,Empty)
  -> register Empty on T'
```

Oracle's paired Function constructor is `annotation/constraints.rs:363–389`;
symbolic-only rows have no stack (:431–439), concrete/empty return rows form
their attachment/filter (:451–469). Ordinary argument reversal and return
Effect preservation are `constraints/machine/propagate.rs:226–233,257–263`.
The reviewed prior observer supplies the consumed-filter/current-future lower
rule, reused with its existing limits. Under premise 5, keep's `L_T'(C,P)`
fails the Empty check; drop's `L_T'(C,id)` follows C's empty positive lower
collection and has no corresponding io violation.

A tempting smaller observer through a's own `[io; 'e]` callback would carry
i's PUSH at the observation itself and could reject **both** alternatives.
The symbolic g occurrence is essential to this constructed discriminator.
The note claims only the named difference, not global acceptance of drop.

## Independence, controls, coverage and limits

The successor owns source levels, actual Apply extrusion, retained lambda
domains, local installation and live capture. Oracle independently supplies
nested paired annotation structure and filter semantics. They share Function
polarity and the hypothetical context transport/replay premises. Oracle drops
the self candidate; it is not an executable oracle for upper-only retention.
A checker assuming the new contextual rules would test consistency of those
rules, not prove authentic source formation or selected hygiene meaning.

Derived controls, not executed mutations: erase io/P and the named difference
vanishes; use only the escaping copy instead of f's original root and original
T is not reached; move f's use to boundary level 1 and the induced comparison
is an upper; remove `h a` and there is no constructed C; use different tail
names for a/g and Empty misses T'; observe a instead of symbolic g and both
alternatives may reject. Introduce a return dependency/merge, a concrete lower
at C, or a contextual subsumption rule and the stated discriminator requires
new analysis. Parent metadata itself is not an SCC edge
(`candidate_intrusion.rs:471–480`). The full source graph's SCCs were not
enumerated, so premise 5 is explicit rather than silently proved.

The two-row activation operand is minimal within the strict anchor/fresh
partition; the displayed source is only the smallest route constructed in this
bounded owner trace, not a globally minimized source program. No random seed,
range enumeration, checker, mutation runner, compiler, Cargo, tests, formatter,
benchmark, child or Git mutation ran. No third equivalent toy probe was added.
Commands were bounded `git show <pin>:<path> | nl -ba | sed -n ...`, `rg`,
`git diff --stat <baseline> <pin> -- <dependencies>`, and `git ls-tree`.
CPU time, peak RSS and elapsed wall time were not measured. Reads were
lightweight single shell processes, with no heavyweight compute process.

All listed code/authority dependencies match the primary baseline at the local
pin; only the already-read independent upper-self review was added between
those pins. Live concurrent HIR edits and conflicted shared records were not
used as frozen inputs or modified. Omitted scope: source parse/admission,
actual explicit-formal attachment constructor, exact underlying-port/tail
representation, weighted Value transport, filter installation/restoration,
whole-source SCC/equality trace, memo behavior, termination, rollback, full
Call, hygiene, soundness/principality and production cutover.

Recommended next action: require the authentic explicit formal constructor to
materialize this exact original-root/anchored-copy route and symbolic observer,
then execute its keep/drop mutation once. The open premise is now that coupled
constructor/transport correspondence, not an arbitrary assumption that a
generalized root somehow exposes both rows.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-upper-self-source-root-bridge.md`.
- Baseline: primary `4958aa8d434bb0f2168ffd42f5d21aa2d0316d38`; dependency pin
  `3641e6ff4534e2b18b4bb9c110b1ccb4458267b8`; Oracle
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Dependency delta between the two successor pins: only
  `upper-self-filter-observer-review.md`, newly present blob
  `ab2790932375a0680304befcc15f12533b182a23`. Code/authority dependencies did
  not change. Pinned code blobs: source
  `ba7c39b31c860f025adfcd31bbb184b20d8bbccb`; formal/effect
  `40991e2f545e765ac04efe53422b6337e8f7a45d`; scheme
  `404ff4ae75f99d1854e1dff23bbe42db565012b9`; extrusion
  `0e10d00fc9db845c03d14537a4ae4bcd5fd81a5f`; intrusion
  `ed363d7f0fea060eb19ce188294934e48589d591`; lib
  `2a43bea966b0ee78ec29f90a404e365710f0de97`; Apply
  `bbcc17e8f897e7dcde10d44ee80863fbd67025f4`.
- Review status: frozen, unreviewed producer artifact; no independent
  certification or established theorem promotion.
- Checks already run: bounded pinned owner reads; dependency-delta/blob
  inspection; note-only `git diff --no-index --check /dev/null <note>` with no
  whitespace diagnostics (status 1 denotes the new-file diff). No executable
  semantic check. Primary owns final snapshot revalidation.
- Proposed checkpoint message: `research: derive upper-self original-root and outer-copy incidence`.
- Shared-record deltas left for primary/curator: record the outer-consumer,
  retained-local-root and deeper-use construction; retain explicit-formal
  construction/payload/filter/SCC premises; keep upper-self discharge and
  production gates open. Do not promote this to an admitted counterexample.

Writes stop at this frozen submission.
