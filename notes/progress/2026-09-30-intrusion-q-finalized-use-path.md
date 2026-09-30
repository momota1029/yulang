# Q fixture: finalized scheme use path

Date: 2026-09-30  
Status: source-audited Oracle path; no source/use equivalence claim  
Scope: frozen Yulang2 Oracle at `a58eefc31`, ordinary instantiation after
generalization of `pub f x = x f`

## Distinguish the recursive self-reference from an incoming scheme use

In `pub f x = x f`, the `f` in the body is a live named-self value used while
lowering the definition. The source-lowering inventory records no
`SccEvent::OpenUse` for this fixture. That occurrence is not an ordinary
incoming use of the finalized scheme. The public result records successful
generalization, formatted type `any -> ['a] 'b`, two ordinary quantifiers,
and no surviving recursive bounds; the q row observed during compaction is
therefore not part of the scheme interval reinstalled for this member. See
`2026-09-30-intrusion-powerset-carrier-candidate.md:198–207,758–774`.

The ordinary post-publication path is separate:

1. `quantify_component` collects the generalized component, then finalizes
   each member and calls `set_def_scheme`; see frozen
   `crates/infer/src/analysis/session/instantiate.rs:14–82` and
   `analysis/session/generalize.rs:958–963`.
2. A later `UseResolved` event enters `instantiate_use_batch` and
   `prepare_instantiated_use`; the latter requires a published
   `Def::Let { scheme: Some(..) }` (`analysis/session/instantiate.rs:311–369`).
3. For an ordinary local scheme, the path calls
   `instantiate_scheme_with_roles_and_provenance` with the secondary type
   level and witness inputs (`analysis/session/instantiate.rs:383–455`). A new
   `SchemeInstantiator` is created for each call (`instantiate.rs:81–96,
   516–528`).
4. One per-use TypeVar map freshens ordinary quantifiers and surviving
   recursive binders, then clones the predicate and role constraints; free
   TypeVars without a map entry retain their identity (`instantiate.rs:620–648,
   732–761`). Stack identities use a separate map and unmapped stack identities
   remain shared (`instantiate.rs:741–767`). Pos/Neg/Neu DAG cloning preserves
   within-use sharing, including Function value/effect positions and stack
   weights (`instantiate.rs:788–999`).
5. Only surviving recursive rows add lower/upper subtype constraints for their
   fresh binders (`instantiate.rs:1002–1030`). The published `f` has no such
   rows, so this path does not reinstall q's recursive interval.
6. The cloned predicate is attached to the incoming `use_value`, with the
   implementation choosing direct lower insertion for a structural top-level
   constructor and subtype insertion otherwise; role constraints follow
   (`analysis/session/instantiate.rs:505–524,717–729`). The batch commits its
   queued edges at `:325–335`.

These source facts explain the intended ordinary-use identity policy, but they
do not yet prove fixture-specific use behavior. The available source capture
does not record the exact finalized scheme fields, stack-quantifier count,
free-anchor set, witness paths, or an actual incoming use of this exact `f`.
The direct-lower branch for this Function scheme is inferred from its formatted
shape; a fixture-specific instantiation trace has not confirmed the branch.

## Next proof obligation

Add a concrete incoming-use context for the generalized `f`, and record the
actual finalized scheme fields and one `UseResolved` instantiation: type and
stack quantifier maps, shared free anchors, witness paths, cloned predicate,
and installed use constraints. Then state the exact `Obs_scheme` relation for
that use, including type result, latent effects, diagnostics, and any exposed
provenance. The proof must show independent local identities across two uses
and preservation of intentionally shared anchors. Keep that separate from the
unproved pre-view `q` rewrite/prune preservation theorem and from the
source-generated constraint graph's regular-presentation correspondence.

This is a read-only source audit; no Oracle files or tests were changed or run.
