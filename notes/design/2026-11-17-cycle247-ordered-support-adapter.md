# Cycle247 ordered support adapter review

`GeneralPresenceOrderedSupport247` proves three generic providers without any
heavy source import: distinct target names plus no target in any RHS typed
reads gives SafeOrder; a disjoint protected pool with complete typed RHS
coverage supplies that condition; complete `typeSources` coverage is also
sufficient through the typed-read subset theorem. All three passed strict Lean.

## The two source functions

`GeneralNominalState.typeSources` (GeneralNominalState.lean98–105) and
`GeneralPresenceSubstitutionSupport244.typeSources` enumerate the same
constructors, including incoming/outgoing rowSources inside arrow terms.
Their bodies match constructor by constructor, but no imported equality theorem
between the two names was compiled in this pass. Actual Definitions241.supported
uses the former function; the new generic full-source wrapper uses the latter.
An explicit bridge is still needed in an actual adapter.

`typedReads` deliberately excludes row occurrences. Its members belong to full
typeSources by UsedSupport245.sources_split. Thus a full-source pool certificate
can feed the typed-only law, but the converse is false. Requiring every target
outside a pool that includes private row reads is unnecessarily restrictive:
rows are unchanged in OrderedBlock.solve. The direct typed pool provider avoids
that overrestriction.

## Actual merge inputs are not automatically duplicate-free

GeneralDeclarations.Declaration.inputNames is
`variablesArgs (normalizeArgs declaration.head)` (GeneralDeclarations.lean50–51).
The actual `Pattern.variables`/`variablesArgs` definitions
(GeneralDeclarationPatterns.lean189–197) concatenate lists and do not remove
repeated variable names. Definitions241.entries likewise flatMaps over names;
for a repeated name whose occurrence count is not one, the same lo/hi target
entries are emitted repeatedly. Its coherent theorem permits this and does
not imply target-list Nodup.

Consequently the new support wrapper cannot simply be applied to the raw
entries with an invented Nodup premise. A real adapter should deduplicate the
names or entries, prove that duplicate removal preserves the conjunction of
block equations, and then obtain injective target identity from the existing
slot_names theorem. Alternatively the solver theorem could be generalized to
coherent repeated writes with an appropriate safety proof. Neither extension
is supplied by this note, and duplicate input names must not become a new
source-language rejection.

## Freshness remains the significant operational boundary

Definitions241.entries_fresh excludes private targets from a protected pool;
Definitions241.supported gives RHS support from endpoint coverage. Together
with a legitimate distinct-target representation and the source-function
bridge, they would supply SafeOrder. The actual versioned allocator's Fresh
predicate instead permits a source already present when its key was previously
allocated. It therefore does not imply protected-pool exclusion for a refresh.
For a genuinely new key, Fresh plus nonmembership in allocated and endpoint
coverage gives a possible initial-install route; this is not the reused-target
rebase case.

The relevant actual source modules were inspected as text. They had no cached
oleans in this workspace, so no large closure rebuild was attempted. This note
claims neither an actual Definitions241 application nor source-boundary
coverage, ordering of all reachable states, or solver termination.

## Later verified completion within cycle247

The generic duplicate-removal gap discussed above was subsequently closed by
OrderedDedup247 and OrderedCoherentAdapter247: coherent originals keep exactly
the same block models, while the internal solver receives distinct targets.
OrderedSort247/Prepared247 now provide bounded topological preparation, with
successful preparation preserving the original block and supplying SafeOrder;
a supplied strictly decreasing dependency rank guarantees success. These do
not implement the actual source freshness/rank producer or compile the heavy
Definitions241 adapter. Repeated source input names are not rejected.
