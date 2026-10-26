# Original formal admission: frozen construction adopted and freshly checked

Date: 2026-10-27. Baseline: `6148fc868565617d7db6ef193a6ff164700d88f7`,
branch `yulang3`. Scope: the original Lambda's owner-local formal declaration,
both entry modes, and its actual generated Build consumer. Whole original
soundness and Effect hygiene remain open.

## Provenance and unchanged source

`lean/YulangClosure/OriginalFormalAdmission.lean` is an exact adoption of the
previously stopped, unintegrated construction at
`/workspace/scratch/f98087c7ac1a/formal-admission-r4/project/YulangClosure/OriginalFormalAdmission.lean`.
Its producer was `/root/whole_soundness_route_r4`; the old freeze receipt
records all code/checker writes stopped, no descendants, and no repository
writes. The adopted module is 34,188 bytes, SHA-256
`77230ab7984ee544db16fe4d9663b73f98b9afa9c5d2610fad59c26753d5ac7c`.
No bytes of that module were modified during adoption.

Every one of the old nineteen mathematical input modules and the three
project configuration files matches the present baseline's SHA-256. The old
eight checker bundles and their failures remain preserved at their original
paths. Their receipt is provenance, not the fresh verification claimed here.
The old complete census has SHA-256
`160ee7cf45a75f4182efa5495449b139f1b973ef52c731545a49e2ac7e66895f`.

The governing original claim is Source Generalize §3.3 and §5.2 in
`2026-10-08-source-generalize-definition-and-proof.md`: a Parameter declares
its ordinary contract in the complete pre-invocation telescope, while
ViewLogic and the event's own proof witnesses retain their separate scopes.
The selected local entry rules are the actual Lambda/Shared constructors in
`OriginalSourceGeneration` and `OriginalFormalShared`; neither was changed.

## Constructed conclusion

All authored declarations are in `YulangClosure.OriginalFormalAdmission`.
`Introduction` retains the original raw Parameter, occurrence route and the
entire typed prior `Telescope`. Its selection is computed by the original
`FormalAssignment`, before any invocation or returned argument exists.

`declarationFor` constructs the actual logical payload: Value entry writes
the selected descriptor and Computation entry writes its selected interface.
`value_description_is_original_producer` and
`computation_description_is_original_producer` identify these packets with
the pre-existing source producers. `ViewPacket` retains independent view,
assignment and witness fields and has no editable Desc fields.

The main theorem, `actual_build_from_whole_telescope`, has the following
logical shape, with its full type printed in the fresh census:

```text
Introduction + FormalAssignment + original Inputs/RuntimeReadout/admissions
  + original Kernel + complete Prior + optional source annotation
  + Satisfies(localKernel, priorEnvironment, actual original Lambda Build)
  -> exists the actual description and view witnesses,
     description = the source-produced selected-contract packet,
     view = a source-owned ViewPacket,
     and for every independently admitted invocation,
       exists its actual admitted receipt and decoded entry state,
       the state's formal contract = the pre-invocation selected contract,
       and the actual enteredBody Judgment holds there.
```

The selected contract and desired final endpoint equation are conclusions;
neither is supplied as a hypothesis. `actual_build_selects_formal` proves the
same constructor result at an already decoded original environment.
`value_entry_body_keeps_contract` and
`computation_entry_body_keeps_contract` then invert the real entry/Shared
rules and preserve that contract into the arbitrary original checked body.
Value entry uses the independently admitted actual Return; Computation entry
retains its carrier without inventing a Force.

Every Runtime constructor's source admission and goal-indexed checking
admission is unchanged, as proved by `runtime_admission_unchanged` and
`checking_runtime_admission_unchanged`. The ordinary current-world fields,
raw event identity, anchors, publication records and independent proof-field
variation are retained. No semantic membership, completed world, successful
query or body-safety proposition is stored in a declaration packet.

## Exact remaining original owners

This is an owner-local registration. `localAdmissions` receives its
`Introduction` externally and dispatches locally using the existing flat
Binder. It does not construct a global route-sensitive original Kernel.
`distinct_routes_same_flat_binder` retains the different source coordinates;
`no_erased_owner_singleton_admission` proves that one erased admission cannot
uniquely select two distinct contracts. No freshness of raw Site identifiers
or global occurrence recovery is assumed.

The original body EventProof admission is unchanged by this module. Its
descriptor-write ownership is therefore a separate next constructor, handled
in `OriginalSourceClosure` rather than silently claimed here. The actual
formal contract's relationship to a call's inlet/view, its returned value or
retained carrier certificate, and the full world at the decoded native event
also remain separate. Completed finite Checking is not an action on arbitrary
hole-relative Background membership. The general recursive L4 theorem, full
primitive/operation/State contracts, future-event coverage, and native solver
success to one same-source-scope joint solution remain open.

## Fresh verification

The primary rebuilt `OriginalRetainedParameter` and `OriginalFormalAdmission`
against this checkout. The worker then ran the exact native pinned executable:

```text
/workspace/scratch/f98087c7ac1a/toolchains/lean-4.35.0-linux/bin/lake
  env lean -j1 -M1024 YulangClosure/OriginalFormalAdmission.lean
```

The first direct attempt failed solely because the retained-parameter import
had not yet been built. After the primary's dependency build, the direct
source check exited 0 with no diagnostics. No worker wrote the shared cache.

A separate fresh audit used the same executable and imported the primary's
current artifact. It enumerated every actual originating declaration, printed
each complete type, collected its transitive axioms, rejected project axioms,
and checked all thirty-five public roots. It also reran the seven small
independent representation probes from the old audit. The fresh audit exited
0 with no diagnostics: 128 module-origin declarations, including 61 theorem
constants, plus fourteen audit-origin declarations including seven theorems.

The actual axiom union is exactly `propext`, `Classical.choice`, and
`Quot.sound`. `actual_build_from_whole_telescope` and both entry/body
preservation theorems use all three; `no_erased_owner_singleton_admission`
uses only `propext`. No `sorryAx`, additional project axiom or native
evaluation assumption occurs in the audited cone.

Fresh audit source and complete output are retained at
`/tmp/yulang-soundness-20261027/AuditFormalAdmission.lean` and
`/tmp/yulang-soundness-20261027/formal-admission-audit.log`.
The module and this note are frozen for independent review. Their adoption
does not promote any parent theorem or authorize a compiler change.
