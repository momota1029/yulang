# R7 source-allocation conditional proof repair — revision 2

Owner: `/root/effect_permission_source_allocation_r7_lean` (registered lean_prover leaf).
Status: **constructed but unchecked**. Lean bytes frozen; all writes stopped after
this handoff. No kernel acceptance, axiom result, independent review, source/native
correspondence, or production closure is claimed.

## Fixed inputs and scope

Contract SHA-256: `eeeca49694bf07518c8277f1d791ca907cc56d5ccdbbc886eab4ed16368942f2`.
R7 manifest SHA-256: `76c23bef7ffccd76740ad65cf06899bbcc0bbd9a63e995406240825af9c69983`.
Baseline R6 Lean SHA-256: `08a45daffede0bbc126d1f6da087c70a6c6abcd22be9ed9bdb7f8d1400c68b10`.
Current Lean SHA-256: `5f11254fe698905a4d1a24ccb9cfe799058a55a27c9bc01dd66033548d49e6b4`.
R5 dependency SHA-256: `ea97baf7c98becef27df9e0c416d8d5fb00e9e1b5b63f37021b01598231936dc`.
R6 source handoff actual SHA-256:
`f2a0b85bd67027f62c0e7ecd77793e88ecf0cd47e0e7f9c5cea05850f859efa9`.
The dispatch message spells that hash differently; the actual file and R7 contract
agree on the hash printed here. The primary previously verified manifest pins.
Source owners remain `candidate_effect.rs` SHA-256
`1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`
and `lib.rs` SHA-256
`ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`.

Read root AGENTS.md, AGENTS.pre-sprint.md, rules/goal-driven-sprints.md,
Lean proof SKILL.md and references/sources.md plus references/execution.md,
current snapshot, loop README, R7 contract/evidence, R6 source/proof handoffs,
R6 actual stdout/status/time, exact Lean dependency definitions and project
configuration/README. No scheduling or Git action was taken.

Original parent: `notes/theory/2026-10-13-intrusion-source-preservation-proof.md`
§§1,3,5, corrected by `notes/design/2026-10-24-birth-level-scc-intrusion.md`
§§2–6. It retains every supported original source program, lawful finite
construction history, actual occurrence, complete source scope and one shared
source-scoped witness. This fragment does not narrow that parent.
Effect policy: `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`
§1–§1.1: composed variance, actual concrete identity, local handling permission
and actual inflow remain distinct. Research drafts are not semantic authority.

Source mapping: `candidate_effect.rs:1617–1691` is the successful value-pair
return cut; `1694–1744` supplies the selected omitted and negative nonempty
concrete ports; `lib.rs:10487–10517` is the successful four-vector fresh push.
Actual definitions inspected in FormalPermissionExportWitness.lean include
`PortDecoded`, `decodePort`, `ValueDecoded`, `TupleDecoded`, `decodeValue`,
`decodeTuple`; the R5 import retains the exact tree/code/output and universal
State equations.

Represented cases: Int/Unit atoms; ordered nonempty Tuple with every element
row omitted; Function argument at !p and result at p, followed by argument then
result effect ports; omitted ports and negative nonempty concrete rows without
variables. Empty tuple traversal is internal only. Variables, holes, other
atoms, positive concrete ports, failed tuple guards, helper failures and enclosing
annotation propagation remain outside this transcription; none is removed from
the original language claim.

## Material candidate repairs

- `Allocator.push`: replace malformed multi-line comma record update with one
  field per line; append semantics and permission preservation are unchanged.
- Change the comment preceding the mutual inductive block from a declaration
  doc comment to an ordinary comment; Lean rejects attaching that doc comment
  to `mutual`.
- `port_decoder`: eliminate directly on its two `SourcePortSuccess` constructors,
  normalize using the supplied helper equalities and fresh-step equations, then
  decode the known port. This avoids the failed dependent elimination of an
  unrelated expanded `PortEvent` case; no premise or conclusion is changed.
- Function decoder proof: perform decoding simplifications in dependency order,
  rewriting the argument-port output before matching the result-port decoder.
- All four mutually recursive decoder/allocation theorems now state explicit
  `termination_by structural run`. This is a candidate repair for the actual R6
  mutual-recursion kernel application mismatches; it remains unverified.
- Rename the reserved local identifier `at` to `argumentTrace`. The same ordered
  AllocationTrace.append composition is retained, including tuple recursion.
- No theorem statement, inductive constructor, source guard, variance, fragment,
  hypothesis or successful-return cut was deliberately changed.

## Exact candidate theorem declarations

All following names have namespace prefix
`YulangClosure.FormalPermissionSourceAllocation` (including AllocationTrace.append).
These are source declarations, **not printed or kernel-accepted types**.

```lean
theorem fresh_success_ordinal {α β γ δ : Type} (bounds : List α)
    (levels : List β) (metadata : List γ) (marks : List δ)
    (b : α) (l : β) (m : γ) (z : δ)
    (_ready : FreshReady bounds.length)
    (hl : levels.length = bounds.length)
    (hm : metadata.length = bounds.length)
    (hz : marks.length = bounds.length) :
    bounds.length < 2^32 ∧
    (bounds ++ [b]).length = bounds.length + 1 ∧
    (levels ++ [l]).length = bounds.length + 1 ∧
    (metadata ++ [m]).length = bounds.length + 1 ∧
    (marks ++ [z]).length = bounds.length + 1
```

```lean
theorem nonallocating_helpers_frame {s t : Projection} (frames : HelperFrames s t) :
    s.effectLength = t.effectLength ∧ s.permissions = t.permissions
```

```lean
theorem AllocationTrace.append {n m k : Nat} {xs ys : List Nat}
    (a : AllocationTrace n xs m) (b : AllocationTrace m ys k) :
    AllocationTrace n (xs ++ ys) k
```

```lean
theorem fresh_step_equations {n : Nat} (a : FreshStep n) :
    a.ordinal = n ∧ a.next = n + 1 ∧
    (a.before.push a.level).permissions = a.before.permissions
```

```lean
theorem source_port_event {c : Context} {p : Bool} {row : Option SourceRow} {s : State}
    {code : SourcePort} {out : PortResult} {births : List Nat}
    (run : SourcePortSuccess c p row s code out births) :
    PortEvent c p code s out births
```

```lean
theorem port_decoder {c : Context} {p : Bool} {row : Option SourceRow} {s : State}
    {code : SourcePort} {out : PortResult} {births : List Nat}
    (run : SourcePortSuccess c p row s code out births) :
    ∃ d, decodePort c p code s = some d ∧ d.out = out ∧ d.births = births
```

```lean
theorem source_pair_decoder_correspondence {c : Context} {p : Bool} {a : Annotation}
      {code : ValueCode} {s : State} {out : ValueDecoded c p s}
      (run : SourcePair c p a code s out) : decodeValue c p s code = some out
```

```lean
theorem source_tuples_decoder {c : Context} {p : Bool} {xs : Annotations}
      {code : TupleCode} {s : State} {out : TupleDecoded c p s}
      (run : SourceTuples c p xs code s out) : decodeTuple c p s code = some out
```

```lean
theorem source_port_allocation {c : Context} {p : Bool} {row : Option SourceRow}
    {s : State} {code : SourcePort} {out : PortResult} {births : List Nat}
    (run : SourcePortSuccess c p row s code out births) :
    AllocationTrace s.nextEffect births out.state.nextEffect
```

```lean
theorem successful_pair_allocation_footprint {c : Context} {p : Bool} {a : Annotation}
      {code : ValueCode} {s : State} {out : ValueDecoded c p s}
      (run : SourcePair c p a code s out) :
      AllocationTrace s.nextEffect out.births out.state.nextEffect
```

```lean
theorem successful_tuples_allocation {c : Context} {p : Bool} {xs : Annotations}
      {code : TupleCode} {s : State} {out : TupleDecoded c p s}
      (run : SourceTuples c p xs code s out) :
      AllocationTrace s.nextEffect out.births out.state.nextEffect
```

```lean
theorem successful_pair_permission_entries {c : Context} {p : Bool} {a : Annotation}
    {code : ValueCode} {s : State} {out : ValueDecoded c p s}
    (_run : SourcePair c p a code s out) :
    ∀ entry ∈ out.entries, Origin out.shape p entry.path entry.allocatedRow entry.metadata ∧
      Owned c entry.metadata ∧ entry.allocatedRow ∈ out.births
```

```lean
theorem r5_source_allocation_instance (s : State)
    (out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s)
    (run : SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out) :
    out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧ out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
    out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
    out.state = {s with nextEffect
```

## Execution, historical failure and remaining parent application

No Lean, Lake, checker, tests, Cargo or compiler command ran in this leaf.
No scratch/cache/generated output was written. Project pin read:
Lean `leanprover/lean4:v4.35.0`, no external dependencies. The primary exclusively
owns fresh R7 audit projects, invocation releases and receipts.

Historical R6 evidence, preserved read-only:
`/tmp/yulang-effect-permission-source-allocation-20261029-r6/lean-receipts/attempt-1/`.
Its stdout reports native Lake `5.0.0-src+eb6cafb` / Lean `4.35.0`, both version
commands exit 0; focused module build exits 1 before theorem/axiom printing.
The skill checker invocation has all 13 roots, --timeout 90, -j1/-M1024 via project
options, one CPU and LEAN_NUM_THREADS=1; overall exit 1, wall 12.21s, max RSS
798448 KiB. First error is record parsing at R6 96:68; further errors at
166,226,236, mutual kernel mismatches,279,283,316 are preserved in full raw stdout.
No axiom audit result exists for this repaired R7 revision. Do not infer that
these candidate edits resolve downstream errors or that a clean build would
instantiate their explicit premises.

Parent-facing application remains `r5_source_allocation_instance`: given the
SAME successful SourcePair witness/output at arbitrary entry State, decoder
uniqueness identifies the exact R5 output and both retained entries jointly,
with births n,n+1,n+2,n+3 and final allocator coordinate n+4. The first remaining
premise is an exact-tree SourcePair witness grounded in actual successful source
execution, including FreshReady/alignment and concrete HelperFrames for every
transitive helper; primary source/native owner retains this obligation.
`HelperFrames` composes supplied equalities, and no concrete Rust helper instance
is established. Full prior permissions-prefix preservation/reattachment, helper
coverage, native State identity (including entry 21), actual allocator availability,
consumer/effect hygiene, unequal transport, soundness, principality, termination
and production remain OPEN. SourcePair existence itself is not proved here.

Only writes: the exact leased Lean file and this handoff. R6 scratch remained
read-only. No root imports, dependency/toolchain files, tests, compiler files,
shared task/status/configuration files, questions, other workers' files or Git
were touched. Audit-1 handoff requests a separately frozen/released primary-owned
invocation; leaf will remain write-stopped until an exact repair lease arrives.
Finite 300-second lane begins with first timestamp 2026-10-29 12:15:44 UTC;
resource use is light read/edit shell commands only, with no build process.


## Revision 2 after actual R7 audit-1 failure

Audit 1 is a primary execution, not a leaf invocation. Full stdout remains at
`/tmp/yulang-effect-permission-source-allocation-20261029-r7/lean-receipts/attempt-1/stdout.txt`.
Lake 5.0.0-src+eb6cafb / Lean 4.35.0 version queries exit 0; the exact focused
module build exits 1. No theorem-type or axiom output was produced. Actual
remaining diagnostics: line 250 `simp made no progress`; line 238 mutual
structural recursion cannot eliminate source_tuples_decoder children; line 283
cannot eliminate successful_pair_allocation_footprint argument.

Candidate repair 2 replaces structural proof recursion with well-founded
recursion on sizeOf code, using constructor size simplification and omega for
subterm decreases. This changes no theorem or relation premise. The Function
proof now separately transports the result-port decoder equation along the
argument-port output equality before simplification. This revision is unchecked.
The 13 source theorem declarations above remain byte-identical. Revision 1's
structural-recursion repair did not succeed; its failure must not be hidden.
All writes stop after this revision; audit 2 requires primary's exact freeze
and release. No audit/checker command was run by this leaf.
