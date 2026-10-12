# Odd/even intrusion: reference probe feasibility and toolchain blocker

Date: 2026-10-12
Status: frozen, unreviewed research; source inspection only, no native execution
Claim class: bounded probe-feasibility characterization; no typing theorem
Yulang baseline: `7b18d2a3f8d88b2b5541c6fed2069f2b694c2e82`
Reference baseline: `9bae772624c23b52a93c1b226157e16898b4d9db`
Reference location: `/home/momota1029/rust/simple-sub-reference`
Owner: `odd_even_intrusion_reference_probe`, researcher leaf; no delegation
Lease: this note and optional `tools/research_odd_even_intrusion_reference_probe.scala`

## Objective and exact premises

The assigned executable question is whether the fixed Term in
[native derivation §2](../theory/2026-10-12-cross-level-odd-even-simple-sub-derivation.md)
still completes when its actual inner `odd(sub n 1)` demand extrusion receives
the approved equalities `C=T` and `D=R`. T is the subtraction result, rather
than the formal B. E is the containing definition-root origin and O the resolved
callee/receiver; their approved Value SCC qualifies this occurrence. These are
the selected meanings in
[approved extrusion-event qualification and definition-root origin](../design/2026-10-12-intrusion-value-type-association.md).
The different helper `C=B`/Record witness is outside this packet.

The context would use the reference's own identity-shared IntType/BoolType
objects and the external integer contracts for `le` and `sub` in the native
derivation. Importing these contracts remains the same conditional source
extension premise as that derivation. This note establishes neither overloaded
Yulang elaboration nor current compiler acceptance of the user's spelling.

**Result: the probe was not executed.** The reference exposes the necessary
source hooks, but no Scala compiler/runtime toolchain was found in the bounded
local search. The primary explicitly prohibited installation, download and a
temporary workspace. Java alone cannot compile these Scala sources. No harness
was written because the optional lease permits it only if it actually runs
against the unmodified reference. Runtime pair identities, post-intrusion bounds,
output and diagnostics therefore remain unobserved. This is a bounded non-result,
not a counterexample to completion or equality preservation.

## Source evidence for a possible probe

Inspection used the pinned reference's actual `shared/src/main/scala/simplesub/`
sources. No transitions were reimplemented or executed in a finite model.

| Owning source | Inspection result and implication |
| --- | --- |
| `Typer.scala:16` | Typer is a non-final class; a subclass can delegate to its implementation. |
| `Typer.scala:48–55,59–83` | `typeLetRhs` and `typeTerm` are public. App delegates recursively, then calls `constrain(f_ty,Function(a_ty,res))`. A wrapper can track the exact retained App object by reference identity, restoring its current-Term frame after child calls. |
| `Typer.scala:88–92,121–126` | `constrain` is public with an explicit mutable test cache. Its level fallback calls the public `extrude` using a newly allocated polar cache. A delegating wrapper can track outer/recursive constrain depth without replacing the cases. |
| `Typer.scala:131–156` | `extrude` receives the actual `(Variable,Boolean) -> Variable` cache. After delegating the outer Function extrusion, the wrapper can inspect that cache and the actual returned Function ports. The source flips polarity for the argument and keeps polarity for the result. |
| `Typer.scala:226–244` | Variables expose their levels and mutable bound lists. The unused private allocation counter need not be intercepted; actual object identities suffice. |
| `TypeSimplifier.scala`, `TyperDebugging.scala` | Reference compacting/simplification and bound traversal are available for result reporting; no alternate simplifier is necessary. |

These hooks make a source-preserving Scala subclass a plausible mechanism.
This statement is based on source declarations, not on a successful subclass
compilation or observed virtual dispatch. A future probe should require all of
the following before it injects anything:

1. The active Term is exactly the inner App object from the fixed native AST,
   with its `odd` lookup resolving to the actual recursive o row.
2. The outer demand is `Function(T,R)`, retaining the actual inferred subtraction
   row and App result row, rather than reconstructing them from names or IDs.
3. The extrusion call is negative at o's level 1; the completed actual cache
   contains exactly `(T,true)->C` and `(R,false)->D` for that occurrence, and
   the returned Function has those same C/D ports. Extra or missing pairs must
   be reported rather than silently discarded.
4. Injection occurs after the complete outer demand constrain returns and
   before the inner App returns into the remaining conditional calculation.
   This is a proposed probe schedule. The authority selects the equalities
   and occurrence, but does not independently select a general SCC schedule.

The reference has no explicit intrusion/union/row-identification operation.
Using `constrain(C,T)`, `constrain(T,C)`, `constrain(D,R)`, `constrain(R,D)`
would exercise its genuine subtype propagation and express two mutual subtype
constraints per retained pair. Each independent invocation should use a fresh
test cache; recursive calls must retain that invocation's cache.

**Unproved encoding premise:** mutual subtype constraints at unequal levels
must faithfully implement the approved equality operation, including later
propagation and generalization. The source comments specify subtyping, not a
leveled equality/quotient theorem. A successful injected run would characterize
that stated encoding and schedule only. It must not be labeled stock Simple-sub
behavior, or be used to prove that this encoding implements selected intrusion.
The unintruded run would use a distinct fresh Typer and the same Term/contracts.

## Toolchain inspection and execution coverage

The build declares Scala `2.13.6` in `build.sbt` and sbt `1.5.5` in
`project/build.properties`. Inspection found no external-library imports in the
six native Typer/type/simplifier helper sources listed below, so an isolated
direct compiler invocation could potentially avoid building the parser, tests,
Scala.js frontend or the whole sbt aggregate. That possibility was not tested.

Exact executable availability check:

```sh
python3 - <<'PY'
import shutil
for name in ('scala', 'scalac', 'sbt', 'scala-cli', 'cs', 'coursier', 'java'):
 print(name + ': ' + str(shutil.which(name)))
PY
java -version
```

Exit status 0. The first six executables were absent from PATH; java was
`/usr/bin/java`, OpenJDK `21.0.12.1`. Two bounded local file searches were run:

```sh
rg --files --hidden /tmp /home/momota1029/.cache /home/momota1029/.ivy2 /home/momota1029/.sbt /home/momota1029/.local/share/coursier 2>/dev/null | rg '(scala-(compiler|library|reflect).*jar|sbt-launch.*jar)$' | head -40
rg --files --hidden /opt /usr/share /home/momota1029/.local /home/momota1029/rust/simple-sub-reference 2>/dev/null | rg '(scala-(compiler|library|reflect).*jar|/scalac$|/scala-cli$|/sbt-launch.*jar)$' | head -45
```

Neither search returned a matching path. Shell pipeline status 0 is not proof
that every search root was present/readable: errors were suppressed and the final
head command controls that status. This is absence within the searched accessible
paths, not a complete machine-wide toolchain inventory. An earlier search of
the cache roots without `--hidden` also returned no matches and adds no stronger
absence claim. No machine-wide search, download, tool installation or temporary
workspace was attempted.

Coverage: one fixed native input planned; zero inference runs; zero enumerated
cases; no seeds, mutations or performance samples. Build budget consumed 0/1;
run budget consumed 0/1. Allowed run bound was 60 seconds and 12 GiB. Local
commands were short read-only inspections; the longest reported search command
took approximately one second. Total agent wall time and peak aggregate RSS were
not measured. A preliminary resource snapshot showed about 27 GiB available RAM
and no heavyweight build among the top RSS processes; this is a snapshot, not
resource isolation or a bound on every concurrent process.

No runtime diagnostic was produced. The prior note's derived `int -> bool`
is not repeated here as an independently executed reference result.

## Frozen dependency evidence and remaining work

Both checkout HEADs matched the supplied baselines during inspection. Reference
`git status --porcelain=v1` was empty before and after inspection. No reference
files, Git index/refs, compiler sources, tests, expectations or configuration
were modified. The persistent reference's six source SHA-256 hashes are:

| Dependency | SHA-256 |
| --- | --- |
| `Typer.scala` | `f968f33615855eaa087a8127d042876867994ca8f1c7dc5d95e9bdd18c43c1e9` |
| `TypeSimplifier.scala` | `618b63f63e71c31890eb36cb18be474bfd31732173c159132306f0e14dc37d2b` |
| `TyperDebugging.scala` | `8f0088c5ff729bb2f787ab2304529c0df5ed0711b29f10bef5398e41cb8a2d6a` |
| `syntax.scala` | `f26f19f6905d42c247198c45da9b1675b22619dd59749047023efe5f7ee3c60f` |
| `helpers.scala` | `c882ea8a565721fb54ee96e38254aeefba721129a5f45eba39fb3399ecb06d2e` |
| `package.scala` | `c33b015e51baf32cb42ca48e6452ab005c85ac185a590ec870c19ef198b4fcb2` |
| Governing association design | `28a0c2aa196912e59e9adb9e62e30d171a03fc485d36314db02c5e13b74f6775` |
| Fixed native derivation | `5a4d89e1c22b553767a6e6789199ec7ef54cafd96216bd1c6b00147d1a1672ad` |

Requested role: researcher. Configured subagent default: `gpt-6.1-sol/high`;
the researcher role file has no model/effort pins. This leaf's task identity is
observed, but effective runtime model/effort metadata was not supplied; those
settings remain unknown rather than inferred from configuration.

Soundness, principality, source admission, normal progress, selected equality
encoding/scheduling, Yulang correspondence, complete Call and F5 replacement
remain OPEN. No independent review or theorem-status promotion is claimed.

Recommended next action: the primary should arrange an authorized cached Scala
2.13 toolchain and isolated output lease, then run one delegating subclass probe
under the original build/run budget, explicitly retaining the equality-encoding
premise. A third supplied-transition model would not remove this execution gap.

## Commit packet

- Exact changed leased path: `notes/progress/2026-10-12-odd-even-intrusion-reference-probe.md`.
- Optional harness path was not created.
- Baseline: Yulang `7b18d2a3f8d88b2b5541c6fed2069f2b694c2e82`;
  reference `9bae772624c23b52a93c1b226157e16898b4d9db`.
- Changed dependency hashes: none observed; hashes above pin the inspected inputs.
- Review status: frozen, unreviewed research checkpoint; source feasibility only.
- Checks already run: read-only HEAD/status/hash inspection, narrow source/API
  inspection, executable availability and two bounded cache searches; no build
  or native execution.
- Proposed commit message: `research: record odd-even reference probe toolchain blocker`.
- Shared-record deltas left to primary/curator: record this execution gap and
  available Typer hooks; keep all parent proof/compiler/cutover gates OPEN.
