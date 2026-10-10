# Pre-materialized view route for q113 return construction

Status: independently reviewed, narrow source-constructor obstruction. No
candidate source was constructed or executed; this does not prove global
impossibility.

The explored alternative was to prepare a view/tail route before captured
bound replay, so the needed return would not depend on restoring a later
direct row bound. The owning implementation separates these operations:
view materialization copies/remaps the descriptor and supplied tail, while
physical row bounds are restored in a later loop. Capture incidence records
ownership but does not add a reverse physical row edge. Annotation tails are
resolved from `(AnnotationScope, name)`, not from an inferred expression row.
Thus the descriptor step does not itself publish a fresh-q→R45 bound.

The independent compiler-referee review passed those owner/source distinctions
and confirmed the report keeps its quantifiers narrow. This attempted route
still needs an ordinary-source supplier for a view tail reaching R45 and an
earlier physical publication connecting q to that tail. No fully specified
candidate met those conditions, so no compiler/source execution was justified.

The frozen analysis is
[`view-constructor note`](/tmp/yulang-source-q113-next-constructor-20261011.md).
Remaining possibilities include other source owners, earlier replay/transport,
and diagnostic rescue; Alternative A/B remains open. No build, source run,
tests, performance sample, or production change resulted from this static
review.
