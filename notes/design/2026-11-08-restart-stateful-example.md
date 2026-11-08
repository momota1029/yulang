# Stateful associated dependency example (2026-11-08)

Status: bounded formal fragment. This is not general source parsing/lowering or B4 saturation.

## Source-level intent (parser/lowering not verified)

The known receiver is a supplied value of type `str`, not inferred from the uniqueness of `Right`.
The following declarations give the complete intended finite constraint example:

```yulang
role Index 'container 'key:
    type value
    our container.index: 'key -> value
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index i = b.value

role Left 'a:
    our x.left: () -> ()
role Right 'a:
    type value
    our x.right: () -> value
role Parent 'a:
    our x.parent: () -> ()
impl Left str:
    our x.left () = ()
impl Right str:
    type value = str
    our x.right () = x
impl Parent (box 'a):
    where 'a: Left, Right
    our x.parent () = ()

my example () =
    my a0 = ("known": str).right ()
    my a1 = (box { value: a0 }).index 0
    my a2 = (box { value: a1 }).index 0
    (box { value: a2 }).parent ()
```

The associated requests are `Right(str, value = a0)`,
`Index(box a1, int, value = a2)`, `Index(box a0, int, value = a1)`.
The first is a known seed; the latter two are visited in reverse dependency order.
First sweep: a1 is not known, so a2 remains pending; a0 is known, so a1 becomes str.
Second sweep: a2 becomes str. Then `Parent(box a2)` has an actual visible dictionary
with both `Left a2` and `Right a2`. Both constraints use the SAME parameter.
This does not infer a type from singleton impl visibility.

The seed Right and final Parent share the same visible Parent/Left/Right registry.
The intermediate Index dependency requests use the existing checked Index registry, not a claim that a common source parser or joint
registry lowering has been proved. Method bodies above explain intent and are
not part of the dictionary theorem. The seed producer is now Right's actual `type value = str`; no ordinary atom is supplied at the entry.

## Formal interfaces

- `Produced s edge out`: receiver materialization, actual declaration `Computed`,
  and output equality. `Step` also represents absence by negating this relation.
- `visit` calls actual `produceIndex`; `sweep` threads the returned state to every
  following edge. `Runs` is an independent inductive execution judgment.
- For all edges, initial states, traces and final states: `sweep = (...)` iff `Runs`.
- `CommonRoleStatefulParentExample.run` performs actual seed, two sweeps,
  ordinary consistency check, endpoint materialization, and actual dictionary
  construction. For every out/argument/answer its successful result iff `Final`,
  which names the explicit finite final state and an independent Dictionary.
- `CommonRoleStatefulIndexPath.run` supports arbitrary finite output paths.
  `run_expected` explicitly assumes a constant-str model and initial str evidence;
  `from_declaration_exact` discharges these from the declaration-generated seed.
  `expected_models` has no consistency premise and characterizes all assignments.

## Not proved

General candidate narrowing, dynamic generation of unbounded/new child graphs,
Paterson/K2-derived saturation termination, syntax-level source lowering,
classification of every none result, and the requested X13–X16 outer entry remain open.
Path termination is finite-list structural recursion. Idempotence is semantic
(model sets), not syntactic equality of accumulated atom lists.

## Review correction and testing boundary

Independent review caught an omitted required Index method body and omitted box declaration in the first draft. The displayed snippet now follows spec 6.2's struct-with impl exactly for those parts, and the Right method returns its associated value so the output binding carries the equality. The explicit function shows the known receiver and each output binding. This is a documented source-level intent, not a proved parser/lowering correspondence: `command -v cargo` found no cargo executable in the environment, and no Rust toolchain installation or parser/typechecker run was performed. The formal requests below the snippet are encoded as checked Lean data, not extracted by a source compiler. No source semantic choice is asserted by this correction.
