# Contextual PUSH self discharge: a future-filter discriminator

Date: 2026-10-10
Status: frozen, unreviewed research; conditional source-owner derivation
Baseline: `b098a46d36170d5d23c8493d8b046cafdcb0ac95`
Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Method: deterministic owning-source derivation; no executable experiment
Production authority: none

## Objective and result

Test whether checking/registering the original annotation filter suffices to
justify dropping `T <: T @ PUSH_i[{io}]` under every later observation.
Governing authority is annotation-effect-hygiene-integration §§1,4–6. The
selected callback target retains its returned `int ->`; it is not exercised
here. The recursive-component note, reviewed one-formal debt certificate and
review, contextual-effect-path-theorem §4, repaired formal-filter-transition
contract, and mixed-debt-observer results retain their existing claim scopes.
Rules research-lab, design-authority and git-concurrency were read in full.

**Conditional discriminator:** an ordinary later empty-effect Function demand
can register `Empty` on the same symbolic Effect row without using the formal
that owns `i`. If the retained self production supplies a stored positive lower
`(T+, PUSH_i[{io}])` at T, that registration reports an `io` filter violation.
After dropping this self production, the same local registration has no such
lower to check and reports no violation. Only one traversal/record is needed.

This refutes keep/drop observational equivalence **for the exact ordinary
lower-bound retention premise below**. It does not establish that dropping is
unsound for the selected language. Retention may itself expose the first
annotation's attachment to an independent symbolic-tail use. Nor does this
prove equivalence for an upper-only successor representation. The current
successor has no contextual formal implementation to execute this comparison.

## Exact hypotheses and typed source route

The hypotheses are explicit:

1. The pinned annotation owners form these Function annotations in one defined
   lambda, resolve nullary `io`, and share the named annotation tail `'e`.
   Source formation reaches the displayed calls without an earlier rejection.
2. Use the pinned ordinary Function child rule, wrapper normalization, and
   current/future positive-lower filter checking. Filter registration is not
   replaced by an invented active-family or source-shape shortcut.
3. In the **keep** alternative, the normalized self candidate is retained as
   an ordinary positive lower at T with its PUSH, after checking/registering
   `{io}` and erasing the consumed filter. Oracle's ordinary Var/Var insertion
   would store both orientations if its two same-variable guards were bypassed.
   This is a candidate retention assumption, not current Oracle behavior or a
   selected successor rule.
4. In the **drop** alternative, only this lower/production is absent. The
   original `{io}` registration and owner fact remain. No unrelated concrete or
   weighted positive lower reaches T in the compared local derivation.
5. The later Empty registration is observed; no earlier resource/proof failure
   or eager infinite replay prevents reaching it. No worklist termination claim
   is made.

A source-shaped producer for the route is:

```yulang
type io
my separate (f: 'c -> [io; 'e] 'c) (g: 'c -> [; 'e] 'c) (accept: ('c -> [] 'c) -> 'c) = accept g
```

This text was not parsed, lowered or executed. Oracle's `type io` is not
identified with the successor's resolved nullary `act io` producer. The
assignment's current successor refuses every explicit formal effect row.

Let F, G, A, C and R be **Value** coordinates for the three formals, shared
written `'c`, and application result. Let T be the **Effect** coordinate for
`'e`, and U the separate **Effect** coordinate of `[]` inside accept's argument
Function. Let i own f's concrete `{io}` attachment and j own the separate empty
attachment. No equation identifies C with T/U, or i with j.

Write N=`Row([],Top)` for the negative absent argument Effect and B=`Bot` for
its positive counterpart. The inspected constructors supply:

```text
Fann+ = Fn(C-, N, Stack(T+,PUSH_i[{io}]),
          NonSubtract(C+,POP_i/filter{io}))
Fann- = Fn(C+, B, Filter(T-,{io}), C-)

Gann+ = Fn(C-, N, T+, C+)
Gann- = Fn(C+, B, T-, C-)

H+ = Fn(C-, N, Stack(U+,PUSH_j[Empty]),
       NonSubtract(C+,POP_j/filter Empty))
H- = Fn(C+, B, Filter(U-,Empty), C-)
Accept+ = Fn(H-, N, B, C+)
Accept- = Fn(H+, B, N, C-)

Fann+ <: F-; F+ <: Fann-
Gann+ <: G-; G+ <: Gann-
Accept+ <: A-; A+ <: Accept-
```

Owners: annotation/constraints.rs:124–138 supplies paired seeds; :251–283
sets the parameter Function boundary; :363–389 constructs all four ports and
result wrappers; :424–470 constructs the nonempty/empty return attachments.
The symbolic-only `[; 'e]` takes :430–439 and adds no PUSH/filter. For `[]`,
:676–685 supplies a fresh PUSH with `Subtractability::Empty`; its negative
return view therefore has an Empty filter. The tail selects T at :602–607 and
the persistent annotation-variable map at :835–845. Annotation/builder.rs:
13–16,386–396 shares surface variable IDs. Defined lambda.rs:665–764 forms all
parameters with the same builder/maps before entering the child body level at
:788; :1244–1307 round-trips those maps. Thus shared T is an owning-source
fact, rather than a freely chosen endpoint equality.

The previously derived paired replay at F yields:

```text
Fann+ <: Fann-
  => Stack(T+,PUSH_i[{io}]) <: Filter(T-,{io})
  => register {io} on T; T+ <: T- @ PUSH_i[{io}]
```

This is the recursive-component note's source-local route, not a new admitted
cycle. Propagate.rs:11–24 prefixes the PUSH, :38–55 consumes the negative
filter, and :258–263 preserves the result Effect context. Entry.rs:1092–1106
and propagate.rs:108–110 actually drop the same-Var candidate in Oracle.

For the body `accept g`, tail.rs:543–563 supplies the application demand
`A+ <: Fn(G+, argEffect+, callEffect-, R-)`. Opposite-bound replay with
Accept+ and ordinary Function argument reversal gives:

```text
Accept+ <: application demand @ identity
  => G+ <: H- @ swap(identity)=identity
  => Gann+ <: H- @ identity
  => T+ <: Filter(U-,Empty) @ identity
  => register Empty on T; T+ <: U- @ identity
```

Replay is bounds.rs:3450–3470 (and the opposite insertion order); argument
reversal is propagate.rs:226–233 and result Effect preservation :258–263.
The upper filter normalization is :38–55. The negative argument Effect is N,
so the `Neg::Bot` pure-passthrough branch is not invoked. U is distinct from T:
`[]` has no named tail; no mixed PUSH/POP cancellation is involved in this
child. All annotations are formed before body entry at the same level; no
generalized fresh use is needed for the displayed route.

The unused f does not supply a body invocation or output POP for i. The
top-level Function formal's output predicate is cleared by lambda.rs:1571–1578.
Its call predicate is stored locally at :919–942 and added by the actual
callee path at tail.rs:550–551,683–703; this body calls accept. It does not
invoke f. Nested j evidence from accept is a distinct empty family and cannot
cancel or manufacture i. These locators explain the incidence; they do not
certify every unrelated lowering/publication path.

## Smallest observation and derivation

The local comparison reduces to one Effect row, one nonempty family, and one
new registered filter:

```text
keep state: Lower(T) contains (Pos::Var(T), left PUSH_i[{io}], All, no right POP)
drop state: that lower is absent
both states: original filter {io} and declared owner fact (T,i,{io}) persist
future event: register Empty on T
```

Bounds.rs:3213–3255 visits each existing lower after new registration;
:3285–3320 performs the same check for future lower insertion. For the keep
lower, `constrain_weighted_pos_lower_by_filter` first checks its left stack.
Row_effect.rs:834–848 traverses active families; :875–932 treats `{io}` as a
concrete family and `Empty` rejects it. The positive Var shape then registers
Empty on T again; the registry's duplicate guard prevents recursive rechecking.
That guard does not undo the already recorded concrete violation.

For the drop state there is no such lower and hence no active `{io}` stack to
check. The declared subtraction fact is not itself a positive lower; the
registry loop reads actual lower records. The local check is vacuous. Original
filter checking therefore does not imply equality under this future event.
Registering Empty first and inserting the retained lower later also
distinguishes the two states by the future-lower path.

Structural controls, derived but not executed: deleting f's concrete head
removes i; renaming g's `'e` disconnects the checked Effect row; deleting the
`accept g` demand removes Empty registration; replacing Empty by `{io}` makes
the named family pass; changing the retention premise to **upper-only** with
no positive lower makes this particular fixture vacuous. These identify the
failure premise and exclude a claim of layout-independent falsification.
Three formals are the smallest source-shaped route constructed here; global
source minimality was not searched. The observer itself is minimal within the
chosen ordinary-lower schema and requires no repeated cyclic expansion.

## Evidence boundary and next gate

Established external results remain the reviewed debt certificate and bounded
mixed observer. New result class: unreviewed conditional source-owner
characterization and finite discriminator under hypotheses 1–5. Retaining the
self lower is a candidate assumption. No admitted Oracle witness, runtime
successor discrepancy, full equivalence theorem, hygiene/principality closure,
support projection, freshening, weighted intrusion or rollback is established.

Pinned successor candidate_extrusion.rs:353–366,641–695 stores one selected
side according to endpoint levels and currently omits equal endpoints without
context. At equal Effect-row levels its selected side would be upper if the
identity omission alone were removed. The lower-record hypothesis above
therefore does **not** follow from those current endpoint operations.
Candidate_source.rs:77–81 and candidate_effect.rs:845–847 reject the required
formal rows before that issue is executable. This is the precise boundary
between the source-schema discriminator and a production falsifier.

No checker ran: a model that supplied these same registration/insertion rules
would verify its inputs, not establish their source admission. Source owners
are independent of the proposed keep/drop algebra, but the derivation and
retention alternative share the stated transition assumptions; there is no
independent execution oracle. No random seeds, enumeration ranges, executable
mutations, Cargo/build/compiler tests, formatter, Git mutation, child agent,
benchmark or timing sample ran. Serial source/hash processes were lightweight;
CPU, peak RSS and total wall usage were not measured. The only write is this
leased note. Ten direct live dependencies matched baseline bytes before write;
concurrent HIR edits were neither consumed nor modified.

Recommended next action: independently review the shared-tail/Empty-demand
owner derivation, then require the chosen successor retention orientation and
filter-observation rule to explain this exact fixture before declaring a
contextual self-discharge theorem. Do not infer a lower record from a grammar
self-loop, or infer safe discharge from Oracle's drop alone. The producer
stopped at the primary's freeze request rather than expanding source search.

## Commit packet

- Exact leased path: `notes/progress/2026-10-10-contextual-self-discharge-falsifier.md`.
- Baseline SHA: `b098a46d36170d5d23c8493d8b046cafdcb0ac95`; Oracle pin:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none in ten checked dependencies. Key SHA-256s:
  authority `ff61df92a84185ef22aecbc6915208fbdee225dc647b51007ea28601e38a70f9`;
  recursive-component `09367bd7bf6f1c962d8b5c2cf5dd6ebcf9ccccc6bd0c606f2744aefbb08dc12b`;
  filter-contract `b18f617be8fad153228bd13578576f957b934d7202a97ba45c3f6618e520a4b2`;
  successor extrusion `34639c30b21699549772e9d4e27513f8bf9c4db999c11bad28a0fff266cf0a5a`.
- Review status: frozen unreviewed research; not independent certification or
  a gate-completion packet.
- Checks already run: pinned `git show` owner reads, authority/dependency
  reads, ten-path read-only SHA-256/live-byte comparison; leased-note whitespace
  check at handoff. No executable checks or measurements.
- Proposed checkpoint message: `research: isolate future-filter PUSH self discriminator`.
- Shared-record deltas left to primary/curator: record the conditional
  lower-retention discriminator separately from a source-admitted witness;
  keep one-sided successor ownership and full contextual self-discharge open.
  No shared task/index/authority, question-board, manifest, lockfile, compiler
  or another worker path was changed.

Writes stop at this frozen submission.
