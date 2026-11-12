# Cycle K2 and completed dictionary selection

Status: Draft proof-interface note, 2026-11-12. Scope: I-22 dictionary side.

Use the nine actual fields of `GeneralNominalCycleBoundary.localFields`, and
quantify the four `Remaining` fields rather than inventing their completion.
The independent V3 local judgment is equivalent to `GeneralNominalCycleK2.Local`
on the journal's context, by existing local projection and extension theorems.
For every such extension, registry, journal, occurrence, tree and dictionary,
`Resolves` plus `Completed (.selected dictionary)` excludes both the actual
cycle-root and inspected-candidate K2 predicates. The same exclusion applies to
every source descendant along actually selected local edges. Conversely, either
K2 witness blocks completed selection, including below the root. For any executor
the returned-tree corollary retains `Exact` and `Checked` explicitly.

The regressions use the existing actual cycle fixtures: `nominalLenRoot` on
`GeneralNominalProgressObstruction.context` rejects (`len (nest 0)` shape), while
`GeneralNominalCycleWrapper.context` has a separate list root outside its record
argument's cycle (`len [loop 1]` shape). The latter selection is lifted from the
full existing selected-local proof, not inferred merely from absence of root K2.
These are semantic graph fixtures, not source-parser executions.

Authority: `spec/06-roles.md` K2 decision dated 2026-11-12. Existing audit
`work/dots-audit:notes/audit/x-oracle.md`, X8–X11, does not provide a faithful
Yulang2 recursive-type oracle (X8/X9 dump `loop` with `never`, X10/X11 fail before
K2). No new Yulang2 execution or agreement claim is made.

This reduces the I-22 policy obligation; it does not fill any new B4 bridge,
construct a concrete executor, prove graph observation completeness, or prohibit
raw reconstruction/Evidence alone from constructing a payload. Those predicates
are deliberately distinct from completed policy-approved selection.

## Focused verification

Lean 4.35.0, with the parent's built imports read-only through `LEAN_PATH`:

- `lean -DwarningAsError=true -o <private-output> Yulang/GeneralNominalCycleDictionaryPolicy.lean`: exit 0, no output.
- `lean -t 0 -DwarningAsError=true Yulang/GeneralNominalCycleDictionaryPolicy.lean`: exit 0, no output.
- `#print axioms` for all twelve new theorems: exit 0; only `propext`,
  `Quot.sound`, and (for the two wrapper-selection theorems) `Classical.choice`.
- `git diff --check`: exit 0.

The initial attempt to pass Lake's `--wfail` to direct Lean was rejected as an
unknown option; the successful direct runs use `-DwarningAsError=true` instead.
The first private audit import also failed because Lean selected the incomplete
private `Yulang` namespace; a read-only symlink overlay of built imports repaired
that search path, without modifying the parent's build cache.
No full build, full verification gate, source-language execution, or external
publication was performed by this worker.
