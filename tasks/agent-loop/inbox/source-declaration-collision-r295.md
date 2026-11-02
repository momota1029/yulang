# R295 abstract declaration collision — revision 1

Producer: `/root/declaration_bridge_review`, under the primary's follow-up lease.
Only new repository paths owned by this packet are this handoff and
`notes/theory/lean/YulangClosure/SourceDeclarationCollisionR295.lean`.
No descendants, Git operations, root-import changes or compiler edits.

Outcome: **constructed and pinned-checker accepted abstract-graph counterexample
to contribution reflection**. Fresh independent review of this new artifact is
still required; the producer does not certify its own construction. This is not
a source-qualified semantics defect and does not refute R295's witness inclusion.

## Original source and parent boundary

Unchanged whole-language parent: `YulangClosure.SourceProblem.InferenceSoundness`
in `YulangClosure/Contracts.lean`, with every supported source, original scope,
generated constraint, solution and the same scoped shared witness. The immediate
review question is whether R295's `retainedRelations` preserves old-node semantics
or only includes old witnesses within its already installed graph.

Governing sources were read in the preceding independent review: authoritative
`2026-10-08-call-source-interface-definition.md` §§2–4 (IF-Insert/IF-Use),
`2026-10-08-native-signature-formation-definition.md` §§2–5, and
`2026-10-24-computed-call-result-constructor.md` §§2–7. The manuscript
`2026-10-24-generated-computed-result-correspondence.md` GR1–GR5 is a claim
locator, not authority to invent an EI interpretation. Their SHA-256 values are,
respectively:

```text
20edc62e798cef22111d0303b71a18b7769060515855fac1b315a5eba37b255c
e6c6cf995a3618172e45b4f8cdf4578313c057c6ec1e3e118c4dc11b6f162ab9
2f3a5461b6dacaa29e881ba8b3003120b912e441dd5e4c47fc4ccaa27d3b31a6
58ab61f7252818e208cc27be29fcc2c7633b35467c47dda0de126fa8bc87544b
```

Frozen direct dependency `SourceDeclarationRetentionR295.lean` remains unchanged:
`deea4e7f8128ab9ad2caf7192bc4cb5b2ae16cc4c5682e01e85e7f13b1d92a1c`.
Its provisional handoff remains unchanged:
`04265891b5336538111b6b40dd8451b75a3395f0f3747601d7dcb76bd2a5c9bb`.
New proof artifact SHA-256:
`f6adeff0b77f8b4fde72f4bb06e4176320911cc071b89d5ef65aba17e94bebc3`.

## Exact construction and declarations

All names here have prefix `YulangClosure.SourceDeclarationCollisionR295`.
The complete original graph has node 0, a licensed primitive, and node 1,
`.insertion 7 9 0 catalogue`. Its child 0 is already registered; this example
needs no dangling edge. `declaration` causes R295 to append the same primitive
at node 2, a new insertion `.insertion 7 9 2 catalogue` at node 3, and the
reference at node 4. The original and new insertion share labels `(7, 9)`.
All packets and joint rows are concrete `Unit` values.

`old` has empty alternative, conjunction and forwarding witness types.
`operators` has empty local operator evidence. The primitive's independent
license is inhabited. No completed old contribution is supplied as an input.
The constructed `newContribution` uses the new global insertion relation at
the old node 1. All judgments below have the same `installed` graph and
`operators`; only the relation family changes.

Complete theorem types, with the namespace prefix omitted from local names:

```lean
old_node_unchanged : installed.node 1 = original.node 1
new_insertion_lookup : installed.node 3 = some (.insertion 7 9 2 catalogue)
old_forward_empty :
  ¬ Nonempty (old.forward (.insertion 7 9) () packet packet)
no_old_contribution :
  DeclContribution installed old operators
    1 () (.insertion 7 9 0 catalogue) packet → False
new_contribution :
  Nonempty (DeclContribution installed
    (retainedRelations original declaration old) operators
    1 () (.insertion 7 9 0 catalogue) packet)
no_reflection :
  ¬ (Nonempty (DeclContribution installed
      (retainedRelations original declaration old) operators
      1 () (.insertion 7 9 0 catalogue) packet) →
    Nonempty (DeclContribution installed old operators
      1 () (.insertion 7 9 0 catalogue) packet))
```

Every theorem's complete transitive axiom list is `[propext]`.
All ten authored definitions were also printed and audited: `catalogue`,
`introduction`, `original`, `declaration`, `installed`, `packet` have `[]`;
`old`, `emptyContract`, `operators`, `newContribution` have `[propext]`.
No project axiom, proof hole, native-evaluation assumption or bypass occurs
in the accepted artifact/audits.

## Verification and evidence

Exclusive scratch/cache remains `/tmp/yulang-r295-independent-review`.
No shared repository cache was written. The isolated snapshot contains the
19-module dependency cone and three unchanged project configuration files;
`collision-inputs.json` records their SHA-256 values. Final comparison found
no changed inputs. Its hash is
`17afcc44449c897d04361fc78f08a73a5675af408616de2822090cc98850cf85`.

The already installed native Lake was resolved by `elan which lake` during
review. Exact native executable:
`/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake`.
Actual versions: Lake `5.0.0-src+eb6cafb` (Lean `4.35.0`); Lean `4.35.0`,
commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

Actual commands, all final exits 0:

```text
python3 .agents/skills/yulang-lean-proofs/scripts/check_lean.py --project /tmp/yulang-r295-independent-review --lake <native-lake> --module YulangClosure.SourceDeclarationCollisionR295 --timeout 120 <six --theorem arguments in collision-checker-command.json>
<native-lake> --no-cache env lean -j1 -M1024 YulangClosure/SourceDeclarationCollisionR295.lean
<native-lake> --no-cache env lean -j1 -M1024 CollisionDefinitionsAudit.lean
```

The helper ran the native version checks, actual module/import build and every
theorem's printed type/axiom audit. Helper wall time: 6.20 seconds; direct file
check: 0.47 seconds; definitions audit: 0.37 seconds. Ordinary `-j1 -M1024`
project limits and `LEAN_NUM_THREADS=1`; no RSS measurement is claimed.
The new module and direct check have no warnings. No broad/default build,
native runtime execution or production correspondence check was performed.

Complete logs and hashes:

```text
c99228276e3170c20fd5b2b5ee836a393749a9dd6416ffb1a85f147c0cce7b4f  collision-checker.log
a067c6303db499f44c04f04ecc1c9a12280801677a34a3ee7701af2c65747a9e  collision-definitions-audit.log
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  collision-direct.log
```

Earlier discovery scratch `CollisionAudit.lean` and `collision-audit*.log`
remain there. Four exploratory elaborations failed on unresolved implicit
graph/catalogue arguments; their error-recovery output included `sorryAx`
and is not accepted proof evidence. The final discovery check and this new
durable module's first build/check passed without holes. Raw failed logs are
preserved rather than replaced by success.

## Parent application and next owner

The counterexample rules out using R295's generic relation extension as an
old-node contribution reflection theorem. Its `retainContribution` still
preserves all old witnesses inside the installed graph, exactly as typed;
`original_node_retained` still preserves old node syntax. Neither theorem
transports arbitrary original-graph semantics or proves that no new old-node
contribution exists.

This example uses unauthenticated graph contracts with an empty forwarding
relation. It is not an instance of lawful original source IF semantics and
does not establish a source-language soundness defect. No original accepted
language case or parent quantifier is removed. Generic source/arm schemas,
EI formation/introduction, legal whole actions and source extraction are
not constructed here. Whole-source soundness, R159 admission, principality,
termination and source/native/production gates remain OPEN.

First remaining owner: the primary's authentic typed source/declaration and
descriptor construction lane, which must establish legal IF actions and actual
EI readouts at the original scopes. Any required preservation/reflection for
that concrete instance needs its own justified premises and proof. The
primary owns fresh independent review and integration of this new artifact.

**Writes stopped after revision 1.** No checker remains active. Only the two
leased repository paths and the exclusively owned scratch directory were
written; frozen R295, shared status and other workers' paths were untouched.
