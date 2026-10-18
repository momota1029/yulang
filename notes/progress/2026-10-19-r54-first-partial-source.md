# R54 source/native audit: first partial-capture discriminator

Status: read-only source-owner trace; bounded positive discriminator, no
parent counterexample. Parent remains OPEN 0→0. R54 contract revision 1,
SHA-256 `b39fbe7287e420c6ff902ea0fa082923f5a820a066f78f547fa49a24b9fd59bd`.
Baseline `96b24b22bd63650964692ef44845c0bc27c376a0`. No code, test, build,
runtime, probe or measurement was performed.

## Candidate and scope

The source-constructor discriminator is:

```text
my outer (q: ['e] int -> ['e] int) = {
  my forward (t:[io] int) = q t;
  forward
}
```

It uses an existing annotated higher-order parameter, a nested parameterized
local function, an Apply, and an ordinary Local use. The source-owner trace
below is conditional on those existing constructors reaching candidate source
execution; no parser, preflight, or whole-solve execution claim is made.
This is outside the original forwarding-preservation positive fragment: the
body forwards `q`'s call result rather than the current computation formal by
direct Name. The positive path therefore cannot instantiate or refute the
parent theorem.

## Owner transition and route

`candidate_source.rs` assigns the enclosing parameter to level 1 and the
nested block initializer to level 2 (`:956–1040`). It records singleton
symbolic formal-effect rows through `FormalEntry` and `FormalAnnotation`
(`:1090–1124,1220–1253`; `candidate_effect.rs:1272–1280,1385–1435`). The
annotation scope interns an effect variable by scope and source name; using
`'e` in both q ports therefore supplies one shared level-1 row, subject to
ordinary source annotation construction.

The `q t` Apply is ordinary source input. In ordinary mode, scoped-callee
recognition and authentication are disabled; native recipe/source-input
identity and normal candidate admission still run (`candidate_source.rs:
1258–1359`; `shadow_apply.rs:1756–1895`). The Apply creates invocation row C
and output-effect row O. Its negative Function demand is extruded to level 1.
Name the positive copy of the provider Name-effect row `b`, the negative copy
of C `c`, and q's shared level-1 effect row `z`. The actual signed port tasks
admit `b <= z <= c`. Apply and Lambda replay then create:

```text
b <= z <= c <= O₂ <= r₂
```

Here the physical bounds are `(b,−,z)`, `(z,−,c)`, `(O,+,c)`, and
`(r,+,c)`. The Apply replay first propagates c into O; the Lambda
result-effect replay then propagates c into r. Structural construction
precedes pending bound snapshots, and successful settlement replays bounds
after merges (`candidate_extrusion.rs:24–30,78,93–167,229–258,330–340`;
`candidate_intrusion.rs:568–713`).

The final `forward` Name invokes the ordinary Local route at boundary 1.
Capture begins from the installed Function root. It expands local t, n, and r
at level 2, while stopping at the shared level-1 rows b and c. It need not
capture C, O, or z: n's captured upper reaches b, and r's retained lower
reaches c. One canonical FreshUse map sends the captured rows to t', n', and
r', leaves b/c shared, and restores `(t',−,n')`, `(n',−,t')`, `(n',−,b)`, and
`(r',+,c)`. The still-live `b <= z <= c` therefore completes the path between
the actual reconstructed ports:

```text
t' <= n' <= b <= z <= c <= r'
```

The capture rule is level above boundary and generic
(`candidate_scheme.rs:755–790,945–1000,1054–1132`); FreshUse allocates one
image per captured canonical row before restoring captured bounds
(`:1555–1615,1715–1755,1860–1906,2153–2183`). This survival depends on the
actual replay-created `(r,+,c)` bound and the live shared middle, not on an
assumed capture of C/O/z.

This is a positive source-qualified instance of route survival, not a general
owner-case proof. It shows why the initially suspected missing edge was not
real: it omitted ordinary Apply/Lambda replay into r. It neither demonstrates
a partial history nor establishes that every actual parent source case has
the same generated replay.

## Remaining judgment and implementation handoff

The first unsupported judgment for the parent application is source-side
generation of the exact same-provider edge through every allowed constructor
history, including the parent’s arbitrary chains, repeated uses, and
simultaneous receivers. R51–R53 and this discriminator cover named histories;
they do not prove that generation induction. The shared-e candidate is outside
the parent's direct-current-formal forwarding fragment, so it cannot discharge
or falsify that judgment. No actual missing reconstructed edge was found in
this candidate.

No safe code slice is identified: the question is the missing general
source-to-native argument, and R54 grants read-only research authority only.
Parent quantifiers, source domain, accepted semantics, expected outputs and
Simple-sub A/B claims remain unchanged. R50 remains NOT ADOPTED.
