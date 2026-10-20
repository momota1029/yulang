# R149 Types/Console dependency closure: source evidence

Status: FROZEN candidate source-native evidence; independent review pending.
Assignment: R149-SOURCE-CLOSURE, revision 1.
Author: `/root/r149_source_closure_proof`; no contributing descendants.
Requested routing: Sol/high (`gpt-6.1-sol`, high); observed model/effort: UNKNOWN.
Authority: R149 rev4 SHA-256 `ba68d22465956972c8d4a2bf55762b25bab9ad689f62f664a3f34ab779b62cd6`;
R149 design `d5f1a924b85df486c33083875fe21d583f2da0bf3f30cf2f6f90d00d60de7001`;
reviewed proof plan `d57681689e4d8b487c9fb749db675ebf1ae5cb008cea47085503208482534861`.
Baseline: `b7b320d0516208ab4f6aeac14b795f99c6f92cce`, tree
`7c2f1f06f1f1f6719e5a88a8854a04f98a7774e7` (primary-provided; no Git invoked).
Oracle dependency: `/home/momota1029/rust/yulang2-oracle-capture`, frozen commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`. Raw bytes of all 34 library
files match every blob ID in rev4, checked with SHA-1 of Git blob framing.
The commit identity itself is supplied by Luna, not independently queried.

## Parent and actual application

The finite parent outcome is unchanged 142-byte Types and 92-byte Console source
through authentic imports, accepted inference, mixed module execution, and exact
ordered host writes. Types SHA-256 is
`8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`;
Console SHA-256 is
`ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`.
Simple-sub/evaluator A/B, R70/R71, soundness, principality, general source/native
correspondence and production admission remain OPEN with their original scope.
No statement here closes independent foreign-continuation quantifiers.

Actual result: the full frozen library closure contains SIX Add implementations
and SIXTEEN Display implementations. A sweep of only num/fmt would miss
`duration:Add`, `instant:Display`, and `path:Display`. The body-demand slice for
the contracted successful selection reaches exactly the three specified builtin
operations, plus the imported host operation `out::write`. This is a conditional
body fact, not a sufficient complete executable-module closure. Imported
initializer obligations and the accepted identity-bound Y3 role selection carrier
are unestablished. R149 code activation therefore remains blocked at those exact
seams, rather than at a need to implement every one of the 59 library builtin
operations immediately.

## Typed dependency and body-demand method

A node identity is `(oracle commit, source path, blob ID, declaration header line,
member/occurrence within declaration)`. Sample nodes use their entire source hash
and occurrence. Numeric DefIds are runtime allocation products: none is invented
here. Re-export edges retain their origin declaration identity; aliases do not
create replacement operations. Candidate identity includes the impl declaration,
role identity, input head, prerequisites, and method requirement/implementation
join. The source-coordinate expected implementations below are not an observed
accepted Y3 selection certificate.

Use two closures. Interface closure I retains authentic import/re-export routes,
all declarations needed to form visible names and signatures, complete candidate
sets for demanded roles, prerequisites, default method bodies and recursive
scheme references. Executable closure E starts at sample expression roots AND
all required computation initializers, then follows accepted references and
selected/default method bodies. Selecting E before constructing I can change
acceptance or ambiguity. Neither closure may infer absent initializers from
absence of a call in the sample. Full declaration bytes remain the authority;
the appendix is a lexical inventory, not a parsed typed interface or validation
of every imported body. An acceptance-preserving slicer is still an implementation
TODO, not an established Y3 feature.

For a candidate-preserving slice, the necessary invariant is: for every demanded
role/method, candidate applicability, prerequisite discharge and implementation
identity agree with the complete accepted environment; ordered required
initializers and every executed body's dependencies also agree. Given that
invariant, traversing ordinary body reference edges yields the leaf set below.
This elementary graph observation does not establish its invariant at an actual
source constructor, solver or consumer.

## Identity-bound graph and Y3 carrier gaps

| Edge | Authentic source evidence | Current Y3 owner and exact unresolved carrier |
|---|---|---|
| Sample -> implicit prelude | Y2 `crates/yulang/src/source/mod.rs::IMPLICIT_PRELUDE_IMPORT`, `source/std_sources.rs::source_with_implicit_std_prelude` and `source/collector.rs::Collector::collect_entry_inner`; source adds environment before lowering | `crates/yu-hir/src/module.rs::SemanticImports` contains only optional opaque `CallerEvidenceBinding`; it certifies no import environment. `tools/inference-playground/src/lib.rs` supplies `SemanticImports::empty`. No authenticated library loader/resolver joins the unchanged source to these imports. Y2's prefixing is evidence of its environment, not permission to rewrite Y3 sample bytes. |
| prelude -> operations/numerics/fmt/IO | `lib/std/prelude.yu` re-exports `std::core::ops::*`, `std::core::*`, `std::num::*`, `std::core::fmt::*`, `std::int::*`, selected `text::str`, `text::path::*`, `std::io::*`, `std::time::*` and other appendix imports | Same missing resolver; retain export visibility and collisions. Prelude also exposes `std::core::id`, so the local `our id` needs actual lexical shadowing, not deleting the imported declaration. `local_source.rs` resolves latest lexical binding before module namespace for simple identifiers, but has no multi-module namespace transport. |
| IO -> console -> host declaration | `lib/std/io.yu` declares console/file/net and re-exports all three. `io/console.yu:4-5` declares `pub host act out`, `write: str -> ()` | `module/source_annotation.rs` operation identities and `LocalSourceForm::Operation` carry local operation references; no demonstrated imported act/operation identity route or host authorization join from this declaration. Do not replace with the spelling `out::write`. |
| Types local polymorphism -> ordered pair | local `id` used at int and str; `answer`, `name`, `(answer,name)` then `pair.say` | `candidate_source.rs::Plan`, `candidate_scheme.rs` fresh-use machinery and `candidate_call.rs` are existing generation/instance/call seams, not a proof of this tuple source. `LocalSourceForm` has no tuple; parenthesized commas are rejected at local_source.rs:1107 and module.rs:1524. `yu-types::PositiveValueView/NegativeValueView` have no tuple or named generic data constructor. No ordered tuple constraint/consumer or runtime tuple value exists in inspected owners. |
| `+` -> Add requirement -> impl | `core/ops.yu:29`, `num.yu:5-6`; full table below | No role/impl candidate, prerequisite or selected method carrier in `LocalSourceForm`, `LocalSourceResolution` or the inspected `candidate_source` interface. Existing call/formal roles are value/computation roles, not Add/Display resolution. Must freeze exact new resolver/solver consumers before a code lease. |
| `.say` / free `say` -> Display -> recursive element show | `core/fmt.yu:23-26` default Display.say; `console.yu:9-11` separate generic free say with Display premise | No source-bound imported role/default-method selection certificate. Keep the two declarations distinct and record actual method lookup. The expected `.say` default route must be demonstrated, including any collision policy with free say; source spelling alone cannot establish it. |
| selected primitives -> runtime | `int.yu:10,15`, `text/str.yu:11`; infer `builtin_ops.rs` and mono-runtime `lib.rs` | `runtime/program.rs::Instruction` and `runtime/machine.rs` lack the three library primitive identity/evaluation owners. Primitive annotation matching in the machine does not implement builtin operations. |
| imported and local initializers -> ordered roots | Y2 lowering `body/methods.rs::commit_provisional_binding` emits ComputedDef iff BindingFetch::from_evaluation runs computation and publication is enabled; root expressions emit RuntimeRoot::Expr. `compiled_runtime.rs` retains/imports runtime_roots; `specializer.rs::specialize_root_exprs` preserves vector order | `runtime/program.rs::from_hir` constructs one HIR's `source_schedule` by expression shape; `machine.rs::start_source_schedule/start` requires a selected DefId. No authenticated cross-module schedule or imported BindingFetch-equivalent classification/order join. |
| host write -> resume -> atomic publication | R149 authority requires resolved `out::write: str -> ()`, exact one payload/unit response/saved continuation, then accepted result publication | `tools/inference-playground/src/lib.rs` rejects RuntimeOutcome::UnhandledRequest. No contracted host adapter; existing operation-v1 continuation evidence is not universal foreign-continuation proof and cannot be reused without its premises. |

## Complete Add candidate inventory in the 34-file environment

Role identity: `lib/std/num.yu:5`, `Add 'a`, requirement `a.add: 'a -> 'a`.
All six have no explicit `where` premise in their source impl. Every head's
nominal type identity and wrapper signature remains an interface dependency.

| Impl identity | Method body dependency | Sample demand |
|---|---|---|
| num.yu:24 int:Add, method :25 | `std::int::add` -> builtin_op::int_add | Console `1+2` |
| num.yu:43 float:Add, method :44 | `std::float::add` -> builtin_op::float_add | retain candidate; no demanded body |
| num.yu:56 frac:Add, method :57 | `std::num::frac::add` -> source frac operations | retain candidate; no demanded body |
| num.yu:69 str:Add, method :70 | `std::text::str::concat` -> builtin_op::string_concat | all newline/format concatenations |
| num.yu:72 list 'a:Add, method :73 | `std::data::list::merge` -> builtin_op::list_merge | retain generic input/scheme; no demanded body |
| time.yu:146 duration:Add, method :147 | `duration_add` :21 -> int add and duration constructor | retain duration identity; no demanded body |

## Complete Display candidate inventory in the 34-file environment

Role identity: `lib/std/core/fmt.yu:23`; `show: str` requirement at :24;
default `say` :25 and `note` :26 carry the actual IO effects. No impl below
overrides `say`. The scalar heads have no explicit where premise.

| Impl identity / show implementation | Prerequisites and body |
|---|---|
| fmt.yu:111 / :112 int | int.to_string -> int_to_string |
| fmt.yu:117 / :118 float | float.to_string -> float_to_string |
| fmt.yu:123 / :124 frac | num.frac.to_string source body |
| fmt.yu:129 / :130 bool | bool.to_string -> bool_to_string |
| fmt.yu:135 / :136 str | identity body |
| fmt.yu:138 / :139 char | text.char.to_string -> char_to_string |
| fmt.yu:141 / :142 unit | literal `"()"` |
| fmt.yu:154 / :156 list 'a | Display 'a at :155; recursive show_list_items :144-152, list_view constructors, list.view_raw, recursive element show, string addition |
| fmt.yu:158 / :160 opt 'a | Display 'a at :159; opt nil/just constructors and inner.show |
| fmt.yu:164 / :167 result 'ok 'err | independent Display 'ok and Display 'err at :165-166; result constructors and both branch show calls |
| fmt.yu:171 / :174 tuple ('a,'b) | independent Display 'a, Display 'b at :172-173; ordered destructuring and four str additions |
| fmt.yu:177 / :181 tuple arity 3 | three independent Display premises :178-180; all components |
| fmt.yu:184 / :189 tuple arity 4 | four independent Display premises :185-188; all components |
| fmt.yu:192 / :198 tuple arity 5 | five independent Display premises :193-197; all components |
| time.yu:143 / :144 instant | instant_rfc3339_utc :108; retains instant/int identities and helper body dependencies when selected |
| text/path.yu:12 / :13 path | bytes.to_utf8_lossy(path.to_bytes p); path/bytes identities; builtin dependencies if selected |

Expected selected impl identities for Types are fmt:171 (pair), fmt:111 (int),
fmt:135 (str), and num:69 (all formatting additions). Console expects num:24
(integer addition), fmt:111 (integer show), and num:69 (newline addition).
These are source-derived expected selections under accepted nominal inputs.
No accepted Y3 DefId/impl join exists yet. Preserve all six/sixteen candidate
records until actual matching and prerequisite discharge establish the selected
identities and ambiguity result. Exact shape matching and tuple arity checks
appear in Y2 `specialize/src/roles.rs::candidate_application` and
`RoleCandidateMatcher`; it materializes candidate prerequisites. This source
fact does not prove an absent Y3 selector implements them.

Y2 `poly/src/roles.rs::RoleImplCandidate` retains impl_def, role, inputs,
associated constraints, prerequisites and requirement/implementation DefId pairs.
`infer/src/instantiate.rs::clone_role_impl_candidate` freshens those type and
prerequisite components while preserving impl/method identities. Y2
`specializer.rs::typeclass_method_instance` collects applicable methods, uses a
default body only with a matched candidate, and reports unresolved/ambiguous
results. The body-only slice must retain recursive schemes and all default
bodies on an actually selected route. It cannot replace a generic scheme with
one sample instantiation. Display pair prerequisites are independent: establishing
int Display cannot discharge str Display by sharing one witness.

## Demanded body edges and leaves

Types: sample local id scheme -> independent calls id 42 and id "Yulang" ->
ordered tuple -> Display.say default -> tuple Display.show -> int Display.show
and str Display.show -> string additions -> authenticated IO write. Pair show
has four concatenations; default say appends newline. If this route is accepted,
the body computes `(42, Yulang)\n` with no additional builtin operation.

Console first root: prelude -> io -> console.println :13 -> str Add ->
str.concat -> out.write. Second root: ops.+ -> int Add -> int.add, then
console.say :9 with Display int -> int.show -> int.to_string -> str Add ->
str.concat -> out.write. These bodies yield respectively `hello from Yulang\n`
and `3\n`, provided ordinary application/receiver evaluation and effect order
are preserved. These reductions do not certify the actual current Y3 path.

The union of builtin leaves of these demanded bodies is
`{int_add, int_to_string, string_concat}`. Types alone does not demand int_add.
The host leaf out.write is separate from those evaluator primitives. Literal,
closure, ordinary application, tuple construction/destructuring, unit response,
and effect continuation operations remain necessary runtime capabilities.
No claim that three evaluator primitives alone implement the complete source
language or full module acceptance follows.

## Imported initializers and order: exact remaining premise

Imported initialization is UNKNOWN, not the empty set. Two obvious top-level
scalar initializers occur at text/str.yu:177 (`split_newline_byte_scan_min = 2`)
and :400 (`word_prefix_small_scan_limit = 512`). All builtin wrapper bindings,
operator bindings, type/role/act bodies, and nested declarations require their
actual admission/classification rather than a textual function heuristic.
The appendix retains every nonempty top-level source line, avoiding a regex
claim that only the two constants can initialize. Neither constant's body calls
an extra primitive; that fact does not establish its schedule membership.

Y2 owner's concrete rule is ComputedDef emission from evaluation classification
and suppression state at commit_provisional_binding; impl declaration lowering
and act declaration lowering explicitly save/set/restore suppress_runtime_roots.
Current Y3 source_schedule uses top-level Apply/If/Catch/Block shape, skipping
other forms. Their equivalence for the complete imported source environment,
including type-body methods, wrappers and inter-module order, is not established.
The source graph also cycles (ops uses num; fmt uses ops/opt/num; fmt default say
uses io; console uses fmt/ops); a naive import topological sort is not a valid
inference of initialization order. Signature cycles need not be executable
initializer cycles. Only an actual source-interface owner can classify them.

Missing artifact for activation: an authenticated ordered initializer list (or
source-qualified no-initializer certificate) for EACH loaded module, with the
source constructor's classification, import-composition order, lazy/cached
value policy and the resulting executable dependency slice. For Types local
answer/name are applications and pair is ordered construction; Console has two
expression roots in source order. Imported roots cannot be dropped because
they are absent from the sample text. No observed full-source typed initializer
list was produced in this packet. Therefore sufficiency of exactly three builtin
leaves for the whole run is UNRESOLVED, even though their sufficiency for the
specified selected sample body slice is established by source inspection.

## Activation application and minimal mutual TODOs

NO_SAFE_CODE_SLICE under this proof lease: neither module.rs::SemanticImports
nor runtime/program.rs::from_hir presently carries the required authenticated
library/candidate/initializer graph. This is a source result, not a request to
edit production code or bypass Simple-sub generation/propagation/generalization.

| Stable request | Owner / required input -> proposed output | Exact falsifier |
|---|---|---|
| R149-CLOSURE-I | Luna resolver/API owner; full frozen 34-file declarations and visibility -> authenticated imports, nominal type identities, six Add/sixteen Display candidates and prerequisite/default-method joins, accepted method IDs for both samples | Omitted candidate changes selected implementation or ambiguity; omitted prerequisite changes acceptance; local id captures imported id |
| R149-CLOSURE-INIT | Luna source-interface/schedule owner; Y2 BindingFetch/evaluation and suppression producers, module collection order, frozen sources -> per-module classified ordered initializer list and Y3 correspondence | Omitted/reordered initializer changes schedule, host events, value, effect or acceptance; unknown treated as empty |
| R149-CLOSURE-E | Luna lowering/runtime owner; accepted I + INIT, selected scheme/body graph -> executable primitive/host leaf certificate and exact instruction owners | Required executed primitive outside the three; unsupported tuple/pattern/operation; body spelling substitutes declaration identity |
| R149-CLOSURE-ACCEPT | Luna solver owner; retained imported interfaces/schemes + ordinary Simple-sub -> accepted inference/public type certificate bound to exact unchanged source and same execution environment | Dropping an unexecuted declaration/body changes acceptance, generalized id instances collapse, role proof silently assumed |

These requests preserve current contract semantics. A new resolver or initializer
policy, code lease or dependency requires Luna's versioned decision before writing.
Fresh review belongs to Luna; this author cannot certify this result. No second
renamed conditional proof is the next step: obtain the typed interface/initializer
owner evidence that can falsify the proposed slice.

Prior work reused: R149 reviewed proof map and authoritative pinned source/outputs;
Y2 candidate/prerequisite and runtime-root representations within their actual
premises. Rejected inference: 34-file module reachability implies all 59 builtin
bodies execute; opposite rejected inference: sample call reachability implies
no imported initialization. R148 finite operation-v1 or hygiene results were
not extended to arbitrary host/foreign continuation cases.

Checks/resources: source reads, raw byte/hash inventory, lexical candidate and
initializer census; no tests, compiler execution, Git, network, production edits,
delegation, or scratch files. Grant 600 seconds charged in full by Luna. Frozen
result produced within the first 300 seconds. STOPPED receipt is in the one
leased inbox. All writers/descendants: this author only, no descendants.

## Frozen source inventories

The following generated census preserves source-coordinate dependency inputs.
Imports and top-level lines are lexical evidence; continuation/member headers
are also retained. It is deliberately not called a typed acceptance certificate.

### lib/std/bool.yu

Blob `cd973c6baefcfa174b72fc356e355dbbfb854bd9`; SHA-256 `2d52be35270f14a487b88608e508aed64860a2f0b3a3843fbc843e9e19e18eb9`.

```text
1: use std::text::str::str
3: pub eq: bool -> bool -> bool = builtin_op::bool_eq
4: pub not: bool -> bool = builtin_op::bool_not
5: pub to_string: bool -> str = builtin_op::bool_to_string
```

### lib/std/control/flow.yu

Blob `7cffe3d504c222f3142b3429eb81543109b0d066`; SHA-256 `8800b16df70d6df4cf45f652bebc57cd9a0428dcd3849a1d852e0a2546a331d8`.

```text
1: pub act sub 'a:
2:     pub return: 'a -> never
3:     pub sub(x: [_] 'a): 'a = catch x:
7: pub act label_sub 'a:
8:     pub return: 'a -> never
9:     pub struct label {
12:     our control_label = label {marker: ()}
13:     pub sub(x: [_] 'a): 'a = catch x:
18: pub act loop:
19:     pub last: () -> never
20:     pub next: () -> never
21:     pub redo: () -> never
24:         our break: () -> never
25:         our judge(x: [_] _) = catch x { break(), _ -> true, _ -> false }
26:         our sub(x: [_] _) = catch x { break(), _ -> (), _ -> () }
30:     pub for_in(xs, f: _ -> [loop; 'e] _): ['e] () =
32:             our loop b = if b: loop:redo::judge:catch f x:
40: pub role LoopLabel 'a:
41:     pub a.last: () -> [_] never
42:     pub a.next: () -> [_] never
43:     pub a.redo: () -> [_] never
45: pub act label_loop:
46:     pub last: () -> never
47:     pub next: () -> never
48:     pub redo: () -> never
50:     pub struct label {
57:         our break: () -> never
58:         our judge(x: [_] _) = catch x { break(), _ -> true, _ -> false }
59:         our sub(x: [_] _) = catch x { break(), _ -> (), _ -> () }
70:         our x.last = label::last(x)
71:         our x.next = label::next(x)
72:         our x.redo = label::redo(x)
74:     pub for_in(xs: 'container, f: label -> 'item -> [label_loop, loop; 'e] _): ['e] () =
75:         where 'container: std::data::fold::Fold 'item
77:             our loop b = if b: loop:redo::judge:catch f control_label x:
```

### lib/std/control/junction.yu

Blob `b746d09d51144d31d9da3bc48f9ec2c270fd4d41`; SHA-256 `63c33098ad7e17c3ac5fdd924d58b57b0e24450f491c9b6a57e127e249e97a9d`.

```text
1: use std::core::ops::*
2: use std::control::flow::*
3: use std::data::fold::*
5: pub act junction:
10:     pub any xs = sub::sub:
15:     pub all xs = sub::sub:
20:     pub junction(x: [_] _) = catch x:
29: pub any xs = junction::any xs
30: pub all xs = junction::all xs
```

### lib/std/control/nondet.yu

Blob `389afb8c66494fb309e448bc9fe80764a0f7b7d6`; SHA-256 `ff04cc3f126fad3e4e828aef629c44b5c6e74ed458f09f55c6199cd3f6507159`.

```text
1: use std::core::ops::*
2: use std::control::flow::*
3: use std::data::fold::*
5: pub act nondet:
6:     pub branch: () -> bool
7:     pub reject: () -> never
8:     pub guard b = if b { () } else { reject() }
9:     pub each xs = sub::sub {
13:     pub x.list = catch x:
18:     pub logic(x: [_] _) = loop x [] [] with:
19:         our loop(x: [_] _, queue, res) = catch x:
30:     pub once(x: [std::control::nondet::nondet; 'e] 'a): ['e] std::data::opt::opt 'a = loop x [] with:
31:         our loop(x: [_] _, queue) = catch x:
39:     pub x.logic = logic x
40:     pub x.once = once x
41:     pub x.guard f = { guard: f x; x }
43: pub use std::control::nondet::nondet::*
```

### lib/std/control/throw.yu

Blob `23465a542a61c2b0870c4f048affd5e4de4c93d7`; SHA-256 `aa6803e6ca976f97229a1697f3baac3e017b660821538a41b66889832f26dd89`.

```text
1: pub role Throw 'e:
2:     type throws
3:     pub e.throw: [throws] never
```

### lib/std/control/var.yu

Blob `ef74a9c2f39fd8e0fe62c3a6ba6eb38554f01f10`; SHA-256 `dc670a126dc9d7abccc9453140ebc1b30c2d9d6c5b1329b5e0841db7fbdff8a2`.

```text
1: pub act ref_update 'a:
2:     pub update: 'a -> 'a
4: pub type ref 'e 'a with:
8:     pub r.update(f: 'a -> 'a): ['e] () =
13: pub act var 't:
14:     pub get: () -> 't
15:     pub set: 't -> ()
```

### lib/std/core.yu

Blob `2b72ccbaf5ec50d5f0ea75ccc3f108e6b3c38642`; SHA-256 `984643783e83bc1bd9c8998fe6b9bcc26a0d3b7606050fb3e37ec5859e8529b7`.

```text
1: pub mod cmp;
2: pub mod convert;
3: pub mod fmt;
4: pub mod ops;
5: pub mod seq;
7: pub id x = x
9: pub compose f g x = f (g x)
```

### lib/std/core/cmp.yu

Blob `b357d106301e56d6fb77a256a08f52b93060ef98`; SHA-256 `03881a76d3a159a23079ff0a1a87dbca42c4c101df47cd61c8f850fcbb7e33a8`.

```text
1: use std::num::frac::frac
3: pub role Eq 'a:
4:     pub a.eq: 'a -> bool
6: pub role Ord 'a:
7:     pub a.lt: 'a -> bool
8:     pub a.le: 'a -> bool
9:     pub a.gt: 'a -> bool
10:     pub a.ge: 'a -> bool
12: impl int: Eq:
13:     our x.eq y = std::int::eq x y
15: impl int: Ord:
16:     our x.lt y = std::int::lt x y
17:     our x.le y = std::int::le x y
18:     our x.gt y = std::int::gt x y
19:     our x.ge y = std::int::ge x y
21: impl float: Eq:
22:     our x.eq y = std::float::eq x y
24: impl float: Ord:
25:     our x.lt y = std::float::lt x y
26:     our x.le y = std::float::le x y
27:     our x.gt y = std::float::gt x y
28:     our x.ge y = std::float::ge x y
30: impl frac: Eq:
31:     our x.eq y = std::num::frac::eq x y
33: impl frac: Ord:
34:     our x.lt y = std::num::frac::lt x y
35:     our x.le y = std::num::frac::le x y
36:     our x.gt y = std::num::frac::gt x y
37:     our x.ge y = std::num::frac::ge x y
39: impl bool: Eq:
40:     our x.eq y = std::bool::eq x y
42: impl str: Eq:
43:     our x.eq y = std::text::str::eq x y
45: impl char: Eq:
46:     our x.eq y = std::text::char::eq x y
48: impl (list int): Eq:
49:     our xs.eq ys = case (std::data::list::view_raw xs, std::data::list::view_raw ys):
```

### lib/std/core/convert.yu

Blob `1eb1c306435091066b00614a7d1f4a2ee08a9353`; SHA-256 `ba8b1c5dbc5bbb324953dc0cf2e267710b84c08638db89da7b757457f72074fb`.

```text
1: pub role Cast 'from:
2:     type to
3:     pub from.cast: to
5: pub cast(p: path): bytes = std::text::path::to_bytes p
6: pub cast(x: int): frac = std::num::frac::new x 1
7: pub cast(x: int): float = builtin_op::int_to_float x
8: pub cast(x: frac): float = std::num::frac::to_float x
```

### lib/std/core/fmt.yu

Blob `fd7b6607094c9ad70bde1fd41890363fa8bd6b31`; SHA-256 `bb36229d7d75008a5ae4fef6c162bbf4bd7dd7ab186cd331fd689daaa71cf212`.

```text
1: use std::core::ops::*
2: use std::data::opt::*
3: use std::num::*
4: use std::num::frac::frac
6: pub enum format_kind = display | debug | lower_hex | upper_hex
8: pub enum format_align = left | right | center
10: pub enum format_sign = plus | minus
12: pub struct format_spec {
21: }
23: pub role Display 'a:
24:     pub a.show: str
25:     pub a.say = std::io::out::write: a.show + "\n"
26:     pub a.note = std::io::err::write: a.show + "\n"
28: pub role Debug 'a:
29:     pub a.debug: str
30:     pub a.dd = std::io::err::write: a.debug + "\n"
32: my repeat(text: str, count: int): str =
38: my format_fill(spec: format_spec): str = case spec.fill:
42: my format_body(spec: format_spec, body: str): str = case spec.precision:
50: my starts_with_minus(body: str): bool =
56: my format_sign_prefix(spec: format_spec, head: str, body: str): str = case spec.sign:
65: my format_with_padding(spec: format_spec, head: str, body: str): str = case spec.width:
93: pub format_display(spec: format_spec, value: 'a): str =
94:     where 'a: Display
97: pub format_debug(spec: format_spec, value: 'a): str =
98:     where 'a: Debug
101: pub format_lower_hex(spec: format_spec, value: 'a): str =
102:     where 'a: LowerHex
106: pub format_upper_hex(spec: format_spec, value: 'a): str =
107:     where 'a: UpperHex
111: impl int: Display:
112:     our x.show = std::int::to_string x
114: impl int: Debug:
115:     our x.debug = x.show
117: impl float: Display:
118:     our x.show = std::float::to_string x
120: impl float: Debug:
121:     our x.debug = x.show
123: impl frac: Display:
124:     our x.show = std::num::frac::to_string x
126: impl frac: Debug:
127:     our x.debug = x.show
129: impl bool: Display:
130:     our x.show = std::bool::to_string x
132: impl bool: Debug:
133:     our x.debug = x.show
135: impl str: Display:
136:     our x.show = x
138: impl char: Display:
139:     our x.show = std::text::char::to_string x
141: impl unit: Display:
142:     our x.show = "()"
144: my show_list_items(xs: list 'a): str =
145:     where 'a: Display
154: impl (list 'a): Display:
155:     where 'a: Display
156:     our xs.show = "[" + show_list_items xs + "]"
158: impl (opt 'a): Display:
159:     where 'a: Display
160:     our value.show = case value:
164: impl (result 'ok 'err): Display:
165:     where 'ok: Display
166:     where 'err: Display
167:     our value.show = case value:
171: impl ('a, 'b): Display:
172:     where 'a: Display
173:     where 'b: Display
174:     our value.show = case value:
177: impl ('a, 'b, 'c): Display:
178:     where 'a: Display
179:     where 'b: Display
180:     where 'c: Display
181:     our value.show = case value:
184: impl ('a, 'b, 'c, 'd): Display:
185:     where 'a: Display
186:     where 'b: Display
187:     where 'c: Display
188:     where 'd: Display
189:     our value.show = case value:
192: impl ('a, 'b, 'c, 'd, 'e): Display:
193:     where 'a: Display
194:     where 'b: Display
195:     where 'c: Display
196:     where 'd: Display
197:     where 'e: Display
198:     our value.show = case value:
201: impl str: Debug:
202:     our x.debug = "\"" + x + "\""
204: impl char: Debug:
205:     our x.debug = "'" + std::text::char::to_string x + "'"
207: impl unit: Debug:
208:     our x.debug = "()"
210: my debug_list_items(xs: list 'a): str =
211:     where 'a: Debug
220: impl (list 'a): Debug:
221:     where 'a: Debug
222:     our xs.debug = "[" + debug_list_items xs + "]"
224: impl (opt 'a): Debug:
225:     where 'a: Debug
226:     our value.debug = case value:
230: impl (result 'ok 'err): Debug:
231:     where 'ok: Debug
232:     where 'err: Debug
233:     our value.debug = case value:
237: impl ('a, 'b): Debug:
238:     where 'a: Debug
239:     where 'b: Debug
240:     our value.debug = case value:
243: impl ('a, 'b, 'c): Debug:
244:     where 'a: Debug
245:     where 'b: Debug
246:     where 'c: Debug
247:     our value.debug = case value:
250: impl ('a, 'b, 'c, 'd): Debug:
251:     where 'a: Debug
252:     where 'b: Debug
253:     where 'c: Debug
254:     where 'd: Debug
255:     our value.debug = case value:
258: impl ('a, 'b, 'c, 'd, 'e): Debug:
259:     where 'a: Debug
260:     where 'b: Debug
261:     where 'c: Debug
262:     where 'd: Debug
263:     where 'e: Debug
264:     our value.debug = case value:
```

### lib/std/core/ops.yu

Blob `575e6fb15ce2d91a39004bbc7b842fedb2d83fdf`; SHA-256 `cb2c15eca2803a6b5a65e33541dd1213bd5f985c470a7767c17a4d59f77ca8c0`.

```text
1: use std::core::cmp::*
2: use std::control::throw::*
3: use std::num::*
5: pub nullfix(return) = std::control::flow::sub::return ()
6: pub prefix(return) 1.0.0 = std::control::flow::sub::return
7: pub prefix(fail) 1.0.0 = \e -> e.throw
9: pub nullfix(last) = loop_last()
10: pub nullfix(next) = loop_next()
11: pub nullfix(redo) = loop_redo()
12: pub prefix(last) 8.0.0 = label_last
13: pub prefix(next) 8.0.0 = label_next
14: pub prefix(redo) 8.0.0 = label_redo
16: pub nullfix (..) = std::data::range::full()
17: pub prefix (..) 8.0.0 = std::data::range::to_included
18: pub prefix (..<) 8.0.0 = std::data::range::to_excluded
19: pub suffix (..) 8.0.0 = std::data::range::from_included
20: pub suffix (<..) 8.0.0 = std::data::range::from_excluded
21: pub infix (..) 4.0.0 4.0.0 = std::data::range::inclusive
22: pub infix (..<) 4.0.0 4.0.0 = std::data::range::range
23: pub infix (<..) 4.0.0 4.0.0 = std::data::range::from_exclusive_to_inclusive
24: pub infix (<..<) 4.0.0 4.0.0 = std::data::range::exclusive
26: pub prefix(not) 8.0.0 = std::bool::not
27: pub prefix (-) 8.0.0 = \x -> std::int::sub 0 x
29: pub infix (+) 5.0.0 5.0.1 = \x -> \y -> x.add y
30: pub infix (-) 5.0.0 5.0.1 = \x -> \y -> x.sub y
31: pub infix (*) 6.0.0 6.0.1 = \x -> \y -> x.mul y
32: pub infix (/) 6.0.0 6.0.1 = \x -> \y -> x.div y
33: pub infix(div) 6.0.0 6.0.1 = std::int::div
34: pub infix(mod) 6.0.0 6.0.1 = std::int::mod
35: pub infix (==) 3.0.0 3.0.1 = \x -> \y -> x.eq y
36: pub infix (!=) 3.0.0 3.0.1 = \x -> \y -> std::bool::not (x.eq y)
37: pub infix (<) 3.0.0 3.0.1 = \x -> \y -> x.lt y
38: pub infix (<=) 3.0.0 3.0.1 = \x -> \y -> x.le y
39: pub infix (>) 3.0.0 3.0.1 = \x -> \y -> x.gt y
40: pub infix (>=) 3.0.0 3.0.1 = \x -> \y -> x.ge y
42: pub lazy infix(and) 2.0.0 2.0.1 = \a -> \b ->
48: pub lazy infix(or) 1.0.0 1.0.1 = \a -> \b ->
54: my loop_last() = std::control::flow::loop::last()
55: my loop_next() = std::control::flow::loop::next()
56: my loop_redo() = std::control::flow::loop::redo()
57: my label_last(label) = label.last()
58: my label_next(label) = label.next()
59: my label_redo(label) = label.redo()
```

### lib/std/core/seq.yu

Blob `716c3747c5ce4757f4000b75792ee05b0d859ca9`; SHA-256 `64a72e1095913f52c4105bcc73493ace22371f71e05af88585225dae81f7067a`.

```text
1: pub role Len 'a:
2:     pub a.len: int
4: pub role IsEmpty 'a:
5:     pub a.is_empty: bool
7: impl str: Len:
8:     our s.len = std::text::str::len s
10: impl (list 'a): Len:
11:     our xs.len = std::data::list::len xs
13: impl str: IsEmpty:
14:     our s.is_empty = std::int::eq(std::text::str::len s, 0)
16: impl (list 'a): IsEmpty:
17:     our xs.is_empty = std::int::eq(std::data::list::len xs, 0)
19: impl bytes: IsEmpty:
20:     our b.is_empty = std::int::eq(std::text::bytes::len b, 0)
22: pub len x = x.len
```

### lib/std/data/fold.yu

Blob `041b9c9cc0160ad6e5a3c4e9512abe298c5d53d1`; SHA-256 `e822e1ba32abd4147179ef580bfcecaeb28027e514d368bda057a6953f88cbd3`.

```text
1: use std::core::ops::*
2: use std::data::opt::*
4: pub role Fold 'container:
5:     type item
6:     pub container.fold: 'acc -> ('acc -> ['e] item -> ['e] 'acc) -> ['e] 'acc
7:     pub container.find: (item -> ['e] bool) -> ['e] opt item = \f -> std::control::flow::sub::sub:
10:     pub container.contains: item -> bool = \target ->
15:     pub container.each: [std::control::nondet::nondet] item = std::control::nondet::each container
```

### lib/std/data/index.yu

Blob `728f69e320b416a06366cf57fb47931db41f8949`; SHA-256 `66c31cd3f83bae43a990c8a79276bd8a6f0020f654a0da2755dcfec10501ada0`.

```text
1: pub role Index 'container 'key:
2:     type value
3:     pub container.index: 'key -> value
```

### lib/std/data/list.yu

Blob `bd1b9b64d61cf5219199bc50275d8da703ecda54`; SHA-256 `f6dc71d39f1b3b965ef2e766ce4749f68b3e3fbdcebe777f13f801b958e83125`.

```text
1: use std::core::ops::*
2: use std::data::opt::*
3: use std::data::fold::*
4: use std::data::index::*
5: use std::data::range::*
6: use std::control::var::*
8: pub enum list_view 'a = empty | leaf 'a | node(list 'a, list 'a)
10: pub type list 'a with:
11:     pub xs.append ys = std::data::list::append xs ys
12:     pub xs.map f = std::data::list::map xs f
13:     pub xs.filter pred = std::data::list::filter xs pred
14:     pub xs.splice r ys = std::data::list::splice xs r ys
15:     pub xs.join separator = std::text::str::join xs separator
16:     pub xs.is_empty = std::data::list::is_empty xs
17:     pub xs.first = std::data::list::first xs
18:     pub xs.last = std::data::list::last xs
19:     pub xs.rev = std::data::list::rev xs
20:     pub xs.sort = std::data::list::sort xs
21:     pub &xs.push x = &xs = $xs.append [x]
23: impl (list 'a): Index int:
24:     type value = 'a
25:     our xs.index i = std::data::list::index_raw xs i
27: impl (list 'a): Index range:
28:     type value = list 'a
29:     our xs.index r = std::data::list::index_range xs r
31: impl (ref 'e (list 'a)): Index int:
32:     type value = ref 'e 'a
33:     our r.index i = ref {
43: pub view_raw: list 'a -> list_view 'a = builtin_op::list_view_raw
44: pub merge: list 'a -> list 'a -> list 'a = builtin_op::list_merge
45: pub len: list 'a -> int = builtin_op::list_len
46: pub index_raw: list 'a -> int -> 'a = builtin_op::list_index
47: pub index_range: list 'a -> range -> list 'a = builtin_op::list_index_range
48: pub index_range_raw: list 'a -> int -> int -> list 'a = builtin_op::list_index_range_raw
49: pub splice: list 'a -> range -> list 'a -> list 'a = builtin_op::list_splice
50: pub splice_raw: list 'a -> int -> int -> list 'a -> list 'a = builtin_op::list_splice_raw
52: my fold_impl xs z f = case std::data::list::view_raw xs:
57: impl (list 'a): Fold:
58:     type item = 'a
59:     our xs.fold z f = fold_impl xs z f
61: pub empty(): list 'a = []
63: pub singleton(x: 'a): list 'a = [x]
65: pub is_empty(xs: list 'a): bool = std::int::eq(std::data::list::len xs, 0)
67: pub cons(x: 'a, xs: list 'a): list 'a = std::data::list::merge(singleton x, xs)
69: pub uncons(xs: list 'a): opt ('a, list 'a) =
76: pub fold xs z f = fold_impl xs z f
78: pub rev(xs: list 'a): list 'a = case std::data::list::view_raw xs:
83: pub map(xs: list 'a, f: 'a -> 'b): list 'b = case std::data::list::view_raw xs:
88: pub filter(xs: list 'a, pred: 'a -> bool): list 'a = case std::data::list::view_raw xs:
94: pub append(xs: list 'a, ys: list 'a): list 'a = std::data::list::merge xs ys
96: pub first(xs: list 'a): opt 'a = case uncons xs:
100: pub last(xs: list 'a): opt 'a = case uncons xs:
106: my sort_split xs x = case std::data::list::view_raw xs:
114: pub sort xs = case xs:
```

### lib/std/data/opt.yu

Blob `956126d039ad4ba05a37aa7af18b51642472bf60`; SHA-256 `c1fe41a74f9c7f6b36bdbf3ca80056ecc78bd62e77ed2e8819ba8f791eb57c1a`.

```text
1: pub enum opt 'a = nil | just 'a
3: pub use std::data::opt::opt::*
```

### lib/std/data/range.yu

Blob `3dcb4336d59ad04ea79b92802749f2f0d5ec57be`; SHA-256 `a7c341ebac7cf7f43a0e548da92fb06caf731f6691f1053abf9498cb1f066f7a`.

```text
1: use std::core::ops::*
2: use std::data::fold::*
4: pub enum bound = unbounded | included int | excluded int
6: pub enum range = within (bound, bound)
8: pub range(start: int, end: int): range =
11: pub inclusive(start: int, end: int): range =
14: pub exclusive(start: int, end: int): range =
17: pub from_exclusive_to_inclusive(start: int, end: int): range =
20: pub from_included(start: int): range =
23: pub from_excluded(start: int): range =
26: pub to_included(end: int): range =
29: pub to_excluded(end: int): range =
32: pub full(): range =
35: pub start(r: range): bound = case r:
38: pub end(r: range): bound = case r:
41: my first_int(b: bound): int = case b:
46: my last_exclusive_int(b: bound): int = case b:
51: my fold_ints(f: _ -> [_] int -> [_] _, i: int, end: int, acc) =
57: my fold_from(f: _ -> [_] int -> [_] _, i: int, acc) =
63: impl range: Fold:
64:     type item = int
65:     our r.fold z f = case r:
```

### lib/std/data/result.yu

Blob `2eb83dbf03da7d0a90bc8e45008160808fabc02f`; SHA-256 `71ff113880bd6f0fb3f3b8d931fb8b508fa1a37d79d7957302d35eace607a7e2`.

```text
1: pub enum result 'ok 'err:
5: pub type result 'ok 'err with:
6:     pub r.map f = std::data::result::map r f
7:     pub r.and_then f = std::data::result::and_then r f
8:     pub r.unwrap_or fallback = std::data::result::unwrap_or r fallback
10: pub map(r: result 'ok 'err, f: 'ok -> 'next): result 'next 'err = case r:
14: pub and_then(r: result 'ok 'err, f: 'ok -> result 'next 'err): result 'next 'err = case r:
18: pub unwrap_or(r: result 'ok 'err, fallback: 'ok): 'ok = case r:
22: pub use std::data::result::result::*
```

### lib/std/float.yu

Blob `c4c9234e891c8d344ba6c7500f0a39c808864624`; SHA-256 `3ae124ddb0b0034e20fff5a97b9ba3dd4e94cd8ba4aad318adcf06444e37a5fe`.

```text
1: use std::text::str::str
3: pub eq: float -> float -> bool = builtin_op::float_eq
4: pub lt: float -> float -> bool = builtin_op::float_lt
5: pub le: float -> float -> bool = builtin_op::float_le
6: pub gt: float -> float -> bool = builtin_op::float_gt
7: pub ge: float -> float -> bool = builtin_op::float_ge
9: pub add: float -> float -> float = builtin_op::float_add
10: pub sub: float -> float -> float = builtin_op::float_sub
11: pub mul: float -> float -> float = builtin_op::float_mul
12: pub div: float -> float -> float = builtin_op::float_div
14: pub to_string: float -> str = builtin_op::float_to_string
```

### lib/std/int.yu

Blob `198b8c2d1ba157e3a9507d1f9353f1bc8df9520c`; SHA-256 `2d0d9b3bba4a4726dbb7f985e46524eea6b7e794759719a78d31984792b79822`.

```text
1: use std::text::str::str
3: pub (mod): int -> int -> int = builtin_op::int_mod
4: pub eq: int -> int -> bool = builtin_op::int_eq
5: pub lt: int -> int -> bool = builtin_op::int_lt
6: pub le: int -> int -> bool = builtin_op::int_le
7: pub gt: int -> int -> bool = builtin_op::int_gt
8: pub ge: int -> int -> bool = builtin_op::int_ge
10: pub add: int -> int -> int = builtin_op::int_add
11: pub sub: int -> int -> int = builtin_op::int_sub
12: pub mul: int -> int -> int = builtin_op::int_mul
13: pub div: int -> int -> int = builtin_op::int_div
15: pub to_string: int -> str = builtin_op::int_to_string
16: pub to_hex: int -> str = builtin_op::int_to_hex
17: pub to_upper_hex: int -> str = builtin_op::int_to_upper_hex
```

### lib/std/io.yu

Blob `4e1852f94f9d5c5c2c47f65bc7b75374a9418f93`; SHA-256 `21c5b06167bbf1ab8363ee0517dfa5f47914d5fba15598392ec64becb70d86e0`.

```text
1: pub mod console;
2: pub mod file;
3: pub mod net;
5: pub use std::io::console::*
6: pub use std::io::file::*
7: pub use std::io::net::*
```

### lib/std/io/console.yu

Blob `8c8eabe69755d28bc66a850745f5ea72c136cd74`; SHA-256 `37e95b1e3b744e5824268f46022b8544f9aeaad8f7532733ad074aef61598a93`.

```text
1: use std::core::fmt::*
2: use std::core::ops::*
4: pub host act out:
5:     pub write: str -> ()
7: pub print value = out::write value
9: pub say(value: 'a): () =
10:     where 'a: Display
13: pub println value = out::write: value + "\n"
15: pub act err:
16:     pub write: str -> ()
18: pub note(value: 'a) =
19:     where 'a: Display
22: pub eprint(value: str) = err::write value
24: pub eprintln(value: str) = err::write: value + "\n"
26: pub dd(value: 'a) =
27:     where 'a: Debug
30: pub act warn:
31:     pub warn: str -> ()
33: pub use warn::warn
35: pub act die:
36:     pub die: str -> never
38: pub use die::die
```

### lib/std/io/file.yu

Blob `f235091cff71fac5600c3601e3ca1646fa82765f`; SHA-256 `ce03a8f7f4e383d8376f164efbde37272f94f82bef09ba01c31ee80f1d550034`.

```text
1: use std::control::throw::Throw
2: use std::data::range::*
3: use std::data::result::*
4: use std::data::opt::*
5: use std::text::path::*
6: use std::control::var::*
7: use std::time::*
9: pub enum file_kind = missing | denied | file | dir | symlink | other
11: pub struct file_meta { kind: file_kind, size: int, readonly: bool, modified: opt instant }
13: pub host act file:
14:     pub load: path -> result str io_err
15:     pub store: (path, str) -> result unit io_err
16:     pub meta: path -> file_meta
17:     pub ambient_touch: path -> result unit io_err
18:     pub ambient_get: path -> str
19:     pub ambient_set: (path, str) -> unit
20:     pub read_at: (path, range) -> result (str, range) io_err
21:     pub write_at: (path, range, str) -> result unit io_err
23: pub error io_err:
29: my unwrap_io(result) = case result:
33: pub meta(path: path): file_meta =
36: pub exists(path: path): bool = case (meta path).kind:
41: pub is_file(path: path): bool = case (meta path).kind:
45: pub is_dir(path: path): bool = case (meta path).kind:
49: pub read_at(path: path, r: range): (str, range) =
52: pub write_at(path: path, r: range, text: str): unit =
55: pub read_text(path: path): str =
58: pub write_text(path: path, text: str): unit =
61: pub text(path: path): ref '[file] str =
72: pub text_with(path: path, f: std::text::str::str -> ['e] ('a, std::text::str::str)): [file, io_err, 'e] 'a =
78: pub use file::*
```

### lib/std/io/net.yu

Blob `5787e6e10df93b90a277d9f6e66ff849200a236c`; SHA-256 `e653f1fe333f08fb51a7aaa0ab3a4af7861a3f157e8044048bdee331d5e9ecb5`.

```text
1: use std::control::throw::Throw
2: use std::data::result::*
3: use std::text::bytes::*
5: pub type listener
6: pub type request_meta
7: pub type respond_slot
9: pub struct request {
13: }
15: pub error net_err:
23: pub host act net:
24:     pub listen: int -> result listener net_err
25:     pub port: listener -> int
27: pub host act server:
28:     pub suspend_multi_shot accept: listener -> request
29:     pub respond: (respond_slot, bytes) -> result unit net_err
31: my unwrap_net(result) = case result:
35: pub listen(port: int): [net, net_err] listener =
38: pub serve(port: int): [net, server, net_err] request =
42: pub type listener with:
43:     pub l.accept(): [server] request =
45:     pub l.port: [net] int =
48: pub type request with:
49:     pub req.respond(res: bytes): [server, net_err] unit =
```

### lib/std/num.yu

Blob `1edbea1b044f8539e263da5de979dee132673ea5`; SHA-256 `631417ef1a85e38564fcc10d17b6eac6f64dfb735bf46d823ef1c7dd015f5e69`.

```text
1: pub mod frac;
3: use std::num::frac::frac
5: pub role Add 'a:
6:     pub a.add: 'a -> 'a
8: pub role Sub 'a:
9:     pub a.sub: 'a -> 'a
11: pub role Mul 'a:
12:     pub a.mul: 'a -> 'a
14: pub role Div 'a:
15:     type out
16:     pub a.div: 'a -> out
18: pub role LowerHex 'a:
19:     pub a.lower_hex: str
21: pub role UpperHex 'a:
22:     pub a.upper_hex: str
24: impl int: Add:
25:     our x.add y = std::int::add x y
27: impl int: Sub:
28:     our x.sub y = std::int::sub x y
30: impl int: Mul:
31:     our x.mul y = std::int::mul x y
33: impl int: Div:
34:     type out = frac
35:     our x.div y = std::num::frac::new x y
37: impl int: LowerHex:
38:     our x.lower_hex = std::int::to_hex x
40: impl int: UpperHex:
41:     our x.upper_hex = std::int::to_upper_hex x
43: impl float: Add:
44:     our x.add y = std::float::add x y
46: impl float: Sub:
47:     our x.sub y = std::float::sub x y
49: impl float: Mul:
50:     our x.mul y = std::float::mul x y
52: impl float: Div:
53:     type out = float
54:     our x.div y = std::float::div x y
56: impl frac: Add:
57:     our x.add y = std::num::frac::add x y
59: impl frac: Sub:
60:     our x.sub y = std::num::frac::sub x y
62: impl frac: Mul:
63:     our x.mul y = std::num::frac::mul x y
65: impl frac: Div:
66:     type out = frac
67:     our x.div y = std::num::frac::div x y
69: impl str: Add:
70:     our x.add y = std::text::str::concat x y
72: impl (list 'a): Add:
73:     our xs.add ys = std::data::list::merge xs ys
```

### lib/std/num/frac.yu

Blob `b8a003efa8177dc064624b40833c4ef38b91564a`; SHA-256 `2d6dbf1cac9d45871cc9fcbe812e6a9999361bdf7d285bab916397a08b3e0939`.

```text
1: pub struct frac { num: int, den: int }
3: my abs(x: int): int =
9: my gcd_positive(a: int, b: int): int =
15: my gcd(a: int, b: int): int = gcd_positive (abs a) (abs b)
17: pub new(n: int, d: int): frac =
26: pub add(x: frac, y: frac): frac =
31: pub sub(x: frac, y: frac): frac =
36: pub mul(x: frac, y: frac): frac =
39: pub div(x: frac, y: frac): frac =
42: pub eq(x: frac, y: frac): bool =
48: pub lt(x: frac, y: frac): bool =
51: pub le(x: frac, y: frac): bool =
57: pub gt(x: frac, y: frac): bool = lt y x
59: pub ge(x: frac, y: frac): bool =
65: pub to_float(x: frac): float =
68: pub to_string(x: frac): str =
```

### lib/std/prelude.yu

Blob `e31685be6f17a516b47c3c29c3a124d7ff1c3682`; SHA-256 `a9d65efddb7d5bb3a8962a2cd64e9bd55a377ec6ff5b3bc29c25db8d1a67b3e0`.

```text
1: pub use std::core::ops::*
2: pub use std::control::throw::*
4: pub use std::core::*
5: pub use std::core::cmp::*
6: pub use std::num::*
7: pub use std::core::fmt::*
8: pub use std::core::seq::*
9: pub use std::core::convert::*
11: pub use std::int::*
12: pub use std::text::str::{
18: }
19: pub use std::text::char::*
20: pub use std::data::fold::Fold
21: pub use std::data::list::*
22: pub use std::data::opt::*
23: pub use std::data::result::*
24: pub use std::text::bytes::*
25: pub use std::text::path::*
26: pub use std::text::parse::parse
27: pub use std::data::range::*
28: pub use std::num::frac::{frac, new}
29: pub use std::control::nondet::nondet
30: pub use std::control::nondet::each
31: pub use std::control::nondet::guard
32: pub use std::data::index::Index
33: pub use std::control::var::*
34: pub use std::control::junction::*
35: pub use std::control::flow::LoopLabel
36: pub use std::io::*
37: pub use std::time::*
38: pub use std::testing::*
```

### lib/std/testing.yu

Blob `0242bdce12bdd21f11248fbd57abee8d33260c69`; SHA-256 `adac62af53c21b9a70d83035f37e265f9415c49510db324680b2884ad3da1f91`.

```text
1: pub lazy prefix(assert) 1.0.0 = assertion::assert
2: pub lazy infix(assert_eq) 1.0.0 1.0.1 = \left -> \right ->
10: pub act assertion:
11:     pub assert: (() -> [_] bool) -> ()
12:     pub assert_eq: (
```

### lib/std/text/bytes.yu

Blob `31489155eee5631307c9b77a02fbf25755aee95f`; SHA-256 `65e0b5b315166fecdf8d5b4abe99c7609416c635098e88f803008d6f104f13bd`.

```text
1: use std::data::index::*
2: use std::data::range::*
3: use std::text::str::str
5: pub len: bytes -> int = builtin_op::bytes_len
6: pub eq: bytes -> bytes -> bool = builtin_op::bytes_eq
7: pub concat: bytes -> bytes -> bytes = builtin_op::bytes_concat
8: pub index_raw: bytes -> int -> int = builtin_op::bytes_index
9: pub index_range: bytes -> range -> bytes = builtin_op::bytes_index_range
10: pub to_utf8_raw: bytes -> (str, int) = builtin_op::bytes_to_utf8_raw
12: pub type bytes with:
13:     pub b.len = std::text::bytes::len b
14:     pub b.is_empty = std::text::bytes::is_empty b
15:     pub b.concat other = std::text::bytes::concat b other
16:     pub b.to_utf8_raw = std::text::bytes::to_utf8_raw b
17:     pub b.to_utf8_lossy = std::text::bytes::to_utf8_lossy b
19: pub is_empty(b: bytes): bool = std::int::eq(std::text::bytes::len b, 0)
21: pub to_utf8_lossy(b: bytes): str = case std::text::bytes::to_utf8_raw b:
24: impl bytes: Index int:
25:     type value = int
26:     our b.index i = std::text::bytes::index_raw b i
28: impl bytes: Index range:
29:     type value = bytes
30:     our b.index r = std::text::bytes::index_range b r
```

### lib/std/text/char.yu

Blob `d879c7d4a5855da0c7581c84b1406f3571cd1756`; SHA-256 `5e453910ccf392a36a4b359d5f03948050a922a64de8ad29fdd7e031ea3d3af2`.

```text
1: use std::text::str::str
3: pub eq: char -> char -> bool = builtin_op::char_eq
4: pub to_string: char -> str = builtin_op::char_to_string
5: pub is_whitespace: char -> bool = builtin_op::char_is_whitespace
6: pub is_punctuation: char -> bool = builtin_op::char_is_punctuation
7: pub is_word: char -> bool = builtin_op::char_is_word
9: pub type char with:
10:     pub c.to_string = std::text::char::to_string c
11:     pub c.is_whitespace = std::text::char::is_whitespace c
12:     pub c.is_punctuation = std::text::char::is_punctuation c
13:     pub c.is_word = std::text::char::is_word c
```

### lib/std/text/parse.yu

Blob `1691990905d51c11cda09cc6059080c6abb7be96`; SHA-256 `b17dce9b9474a3cec830f2c749210e00c752144822836512c928d64d716f5845`.

```text
1: use std::data::list::*
2: use std::data::opt::*
3: use std::core::ops::*
4: use std::text::char::*
5: use std::text::str::str
6: use std::text::bytes::bytes
7: use std::control::var::*
8: use std::data::result::*
10: pub act parse 'item 'err 'pos 'snap:
11:     pub item: () -> 'item
12:     pub fail: 'err -> never
13:     pub eof: () -> bool
14:     pub pos: () -> 'pos
15:     pub cut: () -> ()
16:     pub snapshot: () -> 'snap
17:     pub restore: 'snap -> ()
18:     pub advance: int -> ()
20: pub role ParseError 'err:
21:     pub type item
22:     pub type pos
23:     pub e.merge: 'err -> 'err
24:     pub unexpected: opt item -> pos -> 'err
25:     pub expected: str -> pos -> 'err
26:     pub e.label: str -> self
28: pub struct str_error {
30: } with:
32:         our type item = char
33:         our type pos = (int, int)
34:         our e.merge(f: self) = if e.line < f.line: f
44:         our unexpected(u: opt char) ((l, c): pos) =
46:         our expected(label: str) ((l, c): pos) =
48:         our e.label label = str_error { line: e.line, column: e.column, unexpected: e.unexpected, expected: [label], message: e.message }
50: pub struct prefix_result 'a { value: 'a, rest: str }
51: pub struct match_result 'a { value: 'a, start: int, end: int, text: str }
53: my advance_position(input: str, count: int, line: int, column: int): (int, int) =
60: my advance_position_ascii_chunks(data: bytes, count: int, i: int, line: int, column: int): (int, int) =
68: my advance_position_ascii_loop(data: bytes, count: int, i: int, line: int, column: int): (int, int) =
76: my advance_position_slow_chunks(input: str, count: int, i: int, line: int, column: int): (int, int) =
84: my advance_position_slow_loop(input: str, count: int, i: int, line: int, column: int): (int, int) =
93: pub run_str(input: str, line: int, column: int, parser: [parse char str_error (int, int) (str, int, int)] 'a): result 'a str_error =
117: pub run_prefix_str(input: str, line: int, column: int, parser: [parse char str_error (int, int) (str, int, int)] 'a): result (prefix_result 'a) str_error =
141: pub read_prefix(source: str, parser: () -> [parse char str_error (int, int) (str, int, int)] 'a): result (prefix_result 'a) str_error =
144: my find_from(source: str, start: int, parser: () -> [parse char str_error (int, int) (str, int, int)] 'a): opt (match_result 'a) =
163: pub find(source: str, parser: () -> [parse char str_error (int, int) (str, int, int)] 'a): opt (match_result 'a) =
166: pub edit_once(source: str, parser: () -> [parse char str_error (int, int) (str, int, int)] 'a, replacement: 'a -> ['e] str): ['e] str =
176: pub edit(source: str, parser: () -> [parse char str_error (int, int) (str, int, int)] 'a, replacement: 'a -> ['e] str): ['e] str =
191: pub replace_once(source: str, parser: () -> [parse char str_error (int, int) (str, int, int)] 'a, replacement: str): str =
201: pub replace(source: str, parser: () -> [parse char str_error (int, int) (str, int, int)] 'a, replacement: str): str =
216: pub translate(parser: () -> [parse char str_error (int, int) (str, int, int)] 'a, replacement: 'a -> ['e] str, source: str): ['e] str =
219: pub choice(p: () -> [parse 'item 'err 'pos 'snap] 'a, q: () -> [parse 'item 'err 'pos 'snap] 'a, ()): [parse 'item 'err 'pos 'snap] 'a =
229: pub satisfy(p: 'item -> bool)(): [parse 'item 'err 'pos 'snap] 'item =
237: pub token(expected: str)(): [parse char 'err 'pos 'snap] unit =
247: pub rest(): [parse char 'err (int, int) (str, int, int)] str =
252: pub optional(p: () -> [parse 'item 'err 'pos 'snap] 'a)(): [parse 'item 'err 'pos 'snap] opt 'a = choice(\() -> just (p()), \() -> nil)()
254: pub many(p: () -> [parse 'item 'err 'pos 'snap] 'a)(): [parse 'item 'err 'pos 'snap] list 'a =
260: pub some(p: () -> [parse 'item 'err 'pos 'snap] 'a)(): [parse 'item 'err 'pos 'snap] list 'a =
263: pub label(p: () -> [parse 'item 'err 'pos 'snap] 'a, label_text: str)(): [parse 'item 'err 'pos 'snap] 'a = catch p():
266: pub word(): [parse char 'err (int, int) (str, int, int)] str =
```

### lib/std/text/path.yu

Blob `46a843f6ba24116b472b876b0121135c3cee8179`; SHA-256 `aa05a885d9bec57df63a9330c55c4e6ccb65329f8deee941fa48e29c149c9fab`.

```text
1: use std::text::bytes::bytes
2: use std::core::fmt::Display
4: pub of_bytes_raw: bytes -> path = builtin_op::bytes_to_path
5: pub to_bytes: path -> bytes = builtin_op::path_to_bytes
7: pub type path with:
8:     pub p.to_bytes = std::text::path::to_bytes p
10: pub of_bytes(b: bytes): path = std::text::path::of_bytes_raw b
12: impl path: Display:
13:     our p.show = std::text::bytes::to_utf8_lossy (std::text::path::to_bytes p)
```

### lib/std/text/str.yu

Blob `79e607f994b96b75a9b1d93e1b442d9a8101d44d`; SHA-256 `3ba0fb8e37c7dbfc6ff118611530632d02a9017c8433c10fbcfa2ad4f0c2513b`.

```text
1: use std::core::ops::*
2: use std::data::opt::*
3: use std::data::index::*
4: use std::data::list::*
5: use std::data::fold::*
6: use std::data::range::*
7: use std::control::var::*
8: use std::text::bytes::bytes
9: use std::text::char::char
11: pub concat: str -> str -> str = builtin_op::string_concat
12: pub eq: str -> str -> bool = builtin_op::string_eq
13: pub len: str -> int = builtin_op::string_len
14: pub line_count: str -> int = builtin_op::string_line_count
15: pub line_range: str -> int -> range = builtin_op::string_line_range
16: pub index_raw: str -> int -> char = builtin_op::string_index
17: pub index_range: str -> range -> str = builtin_op::string_index_range
18: pub index_range_raw: str -> int -> int -> str = builtin_op::string_index_range_raw
19: pub splice: str -> range -> str -> str = builtin_op::string_splice
20: pub splice_raw: str -> int -> int -> str -> str = builtin_op::string_splice_raw
21: pub to_bytes: str -> bytes = builtin_op::string_to_bytes
23: pub type lines with:
27: pub type ref_lines 'e with:
30:     pub ls.index i = ref {
43: pub str_line_view(source: str): lines =
46: pub line_view(source: ref 'e str): ref_lines 'e =
49: impl lines: Index int:
50:     type value = str
51:     our ls.index i =
55: impl (ref_lines 'e): Index int:
56:     type value = ref 'e str
57:     our ls.index i = ref {
70: my fold_lines(ls: lines, i: int, end: int, acc, f) =
76: my fold_ref_lines(ls: ref_lines 'e, i: int, end: int, acc, f) =
82: impl lines: Fold:
83:     type item = str
84:     our ls.fold z f = fold_lines(ls, 0, std::text::str::line_count ls.source, z, f)
86: impl (ref_lines 'e): Fold:
87:     type item = ref 'e str
88:     our ls.fold z f = fold_ref_lines(ls, 0, std::text::str::line_count (ls.source.get()), z, f)
90: pub type str with:
91:     pub s.splice r insert = std::text::str::splice s r insert
92:     pub s.find needle = std::text::str::find s needle
93:     pub s.contains needle = std::text::str::contains s needle
94:     pub s.starts_with prefix = std::text::str::starts_with s prefix
95:     pub s.ends_with suffix = std::text::str::ends_with s suffix
96:     pub s.split separator = std::text::str::split s separator
97:     pub s.split_once separator = std::text::str::split_once s separator
98:     pub s.replace_once from to = std::text::str::replace_once s from to
99:     pub s.replace from to = std::text::str::replace_all s from to
100:     pub s.trim = std::text::str::trim s
101:     pub s.trim_start = std::text::str::trim_start s
102:     pub s.trim_end = std::text::str::trim_end s
103:     pub &r.replace_once pattern replacement = (&r).update \s -> std::text::str::replace_once s pattern replacement
104:     pub &r.replace pattern replacement = (&r).update \s -> std::text::str::replace s pattern replacement
105:     pub &r.replace_all pattern replacement = (&r).update \s -> std::text::str::replace_all s pattern replacement
106:     pub &r.splice range replacement = (&r).update \s -> std::text::str::splice s range replacement
107:     pub &r.trim = (&r).update \s -> std::text::str::trim s
108:     pub &r.trim_start = (&r).update \s -> std::text::str::trim_start s
109:     pub &r.trim_end = (&r).update \s -> std::text::str::trim_end s
110:     pub s.repeat count = std::text::str::repeat s count
111:     pub s.to_int = std::text::str::to_int s
112:     pub s.len = std::text::str::len s
113:     pub s.is_empty = std::text::str::is_empty s
114:     pub s.lines: lines = str_line_view s
115:     pub &s.lines = line_view &s
116:     pub s.print = std::io::print s
117:     pub s.println = std::io::println s
118:     pub s.eprint = std::io::eprint s
119:     pub s.eprintln = std::io::eprintln s
121: pub is_empty(s: str): bool = std::int::eq(std::text::str::len s, 0)
123: my starts_with_at_len(source: str, source_len: int, needle: str, needle_len: int, start: int): bool =
130: my starts_with_at(source: str, needle: str, start: int): bool =
138: my find_at_len(source: str, source_len: int, needle: str, needle_len: int, start: int): opt int =
144: my find_at_loop(source: str, source_len: int, needle: str, needle_len: int, limit: int, i: int): opt int =
153: my find_at(source: str, needle: str, start: int): opt int =
156: pub find(source: str, needle: str): opt range =
161: pub contains(source: str, needle: str): bool =
166: pub starts_with(source: str, prefix: str): bool =
169: pub ends_with(source: str, suffix: str): bool =
177: my split_newline_byte_scan_min = 2
179: pub split(source: str, separator: str): list str =
194: my split_generic(source: str, source_len: int, separator: str, separator_len: int): list str =
197: my split_generic_loop(source: str, source_len: int, separator: str, separator_len: int, start: int, out: list str): list str =
214: my split_newline_bytes(source: str): opt (list str) =
230: my split_newline_bytes_chunk(data: bytes, end: int, state: (int, list str, bool), chunk: int): (int, list str, bool) =
239: my split_newline_bytes_step(data: bytes, state: (int, list str, bool), i: int): (int, list str, bool) = case state:
251: pub split_once(source: str, separator: str): opt (str, str) =
264: my join_tail(parts: list str, separator: str, out: str): str =
270: pub join(parts: list str, separator: str): str =
275: my trim_start_index(source: str, i: int): int =
284: my trim_end_index(source: str, end: int): int =
294: pub trim_start(source: str): str =
300: pub trim_end(source: str): str =
303: pub trim(source: str): str =
311: pub repeat(source: str, count: int): str =
322: my digit_value(item: char): opt int =
336: my parse_unsigned_int(source: str, start: int, i: int, acc: int): opt int =
352: pub to_int(source: str): opt int =
364: pub replace_once(source: str, from: str, to: str): str =
380: pub replace(source: str, from: str, to: str): str =
383: pub replace_all(source: str, from: str, to: str): str =
400: my word_prefix_small_scan_limit = 512
402: pub word_prefix_at(source: str, start: int): str =
423: my word_prefix_ascii_or_slow_end(source: str, source_len: int): int =
433: my word_prefix_ascii_chunk(data: bytes, data_len: int, state: (int, int), chunk: int): (int, int) =
442: my word_prefix_ascii_step(data: bytes, state: (int, int), i: int): (int, int) = case state:
453: my ascii_word_byte(byte: int): bool =
459: my word_prefix_slow_end(source: str, source_len: int, i: int): int =
467: my word_prefix_slow_chunk(source: str, source_len: int, state: (int, bool), start: int, chunk: int): (int, bool) =
476: my word_prefix_slow_step(source: str, state: (int, bool), i: int): (int, bool) = case state:
484: impl str: Index int:
485:     type value = char
486:     our s.index i = std::text::str::index_raw s i
488: impl str: Index range:
489:     type value = str
490:     our s.index r = std::text::str::index_range s r
492: impl (ref 'e str): Index range:
493:     type value = ref 'e str
494:     our r.index i = ref {
504: impl (ref 'e str): Index int:
505:     type value = ref 'e char
506:     our r.index i = ref {
```

### lib/std/time.yu

Blob `e87ef48ce7920ca3a80d4903a1d0eefbfdeec80e`; SHA-256 `1ecaa6181213fcac70922579b964bd491947c95ea1cda8ee09cc00f2a081d29f`.

```text
1: use std::core::cmp::*
2: use std::core::fmt::*
3: use std::core::ops::*
4: use std::num::*
6: pub struct instant { epoch_nanos: int }
7: pub struct duration { nanos: int }
9: pub host act clock:
10:     pub now: () -> instant
12: pub instant_add(t: instant, delta: duration): instant =
15: pub instant_sub(t: instant, delta: duration): instant =
18: pub instant_since(later: instant, earlier: instant): duration =
21: pub duration_add(x: duration, y: duration): duration =
24: pub duration_sub(x: duration, y: duration): duration =
27: pub nanos(count: int): duration =
30: pub micros(count: int): duration =
33: pub millis(count: int): duration =
36: pub secs(count: int): duration =
39: pub mins(count: int): duration =
42: pub hours(count: int): duration =
45: pub days(count: int): duration =
48: my floor_div(x: int, y: int): int =
53: my floor_mod(x: int, y: int): int =
56: my civil_from_epoch_days(days_since_epoch: int): (int, int, int) =
68: my pad2(n: int): str =
71: my pad3(n: int): str =
77: my pad4(n: int): str =
86: my pad9(n: int): str =
89: my trim_trailing_zeros(text: str): str =
100: my fraction_text(nanos_in_second: int): str =
106: my instant_rfc3339_utc(x: instant): str =
119: impl instant: Eq:
120:     our x.eq y = std::int::eq x.epoch_nanos y.epoch_nanos
122: impl instant: Ord:
123:     our x.lt y = std::int::lt x.epoch_nanos y.epoch_nanos
124:     our x.le y = std::int::le x.epoch_nanos y.epoch_nanos
125:     our x.gt y = std::int::gt x.epoch_nanos y.epoch_nanos
126:     our x.ge y = std::int::ge x.epoch_nanos y.epoch_nanos
128: impl duration: Eq:
129:     our x.eq y = std::int::eq x.nanos y.nanos
131: impl duration: Ord:
132:     our x.lt y = std::int::lt x.nanos y.nanos
133:     our x.le y = std::int::le x.nanos y.nanos
134:     our x.gt y = std::int::gt x.nanos y.nanos
135:     our x.ge y = std::int::ge x.nanos y.nanos
137: impl instant: Debug:
138:     our x.debug = "instant { epoch_nanos: " + std::int::to_string x.epoch_nanos + " }"
140: impl duration: Debug:
141:     our x.debug = "duration { nanos: " + std::int::to_string x.nanos + " }"
143: impl instant: Display:
144:     our x.show = instant_rfc3339_utc x
146: impl duration: Add:
147:     our x.add y = duration_add x y
149: impl duration: Sub:
150:     our x.sub y = duration_sub x y
152: pub use clock::*
```

## Additional inspected owner byte identities

```text
Y2 crates/infer/src/check.rs f65c78283befa3164b1e314a43ac6cd2a964dd9acb0fc88ddb86644953d819f6
Y2 crates/infer/src/module_table/mod.rs ff002a9eede92aef54bb28f6aedf8ab53d79b959634d70d2ae2f6b36c7da3ef7
Y2 crates/infer/src/instantiate.rs 876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c
Y2 crates/infer/src/lowering/body/methods.rs 0f7d0ac524c4934a4491681e6f9901cdc81f8aff20da7f394888c691bb8c067b
Y2 crates/infer/src/lowering/body/mod.rs f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1
Y2 crates/infer/src/compiled_runtime.rs 9c352576fb01b00d623eae34f32176f5da8af67ed9a69e5bea68e3f371001b58
Y2 crates/poly/src/roles.rs 9e6c5937a84bd6851f12cc31c0a638a2ec4d4bbcad50ef0db1ea2ef4c6bf769e
Y2 crates/specialize/src/roles.rs 50d24afbe7d87733750cc615df5a372ee093edb8329efbf0cab2b68ea8469f58
Y2 crates/specialize/src/lib_support/specializer.rs 6efdb58c5c3ea99506a45b4b5f726775b03352421bb8b4fefe36cc4762e3eeef
Y2 crates/yulang/src/source/mod.rs de29d6bbcbe8a969f7bf77b852cae2c314de1d6158c6cdb7dec8b6022e06d059
Y2 crates/yulang/src/source/std_sources.rs 845c07acb71b812d8501a3ce9934d8aab3e35b874f346ab7d801065957fcaadc
Y2 crates/yulang/src/source/collector.rs 3c8968412eeff12fdd896dc83ae9676c638c1cfcdaf120ecc9ad13980b70868a
Y2 crates/wasm/src/lib.rs f4f59059025a7160179337579060800eb7559f67b5714500a78e7559fc8c286c
Y2 crates/infer/src/builtin_ops.rs c79a7dfb031bc58598ea6551472be568362f3b34c1b7a1b4c53721e0581c053d
Y2 crates/mono-runtime/src/lib.rs 3a821fc693414e6d9feef6d16bf44df4caa13d3b17af137439155b74765a683f
Y2 web/playground/src/main.ts baa040dcd9ac837864b4dd0d8ac6c79bfffc3fe2466bcda43b8db14305dcaf90
Y3 crates/yu-hir/src/module.rs 153a23ecaa68fd150d8bd0cc0316f3723e1cb5d98a6e3026aadef2bfd08fd907
Y3 crates/yu-hir/src/module/local_source.rs d9f516993c579ae8f4dd905abb8400ffc0769072a904a4b4c8d4ffbefcde6442
Y3 crates/yu-hir/src/module/source_annotation.rs b8462b66eac24a48b6fc5e931a3d8b7c38c19bb8b2f1a7cdc4ecd9a8a7a1117f
Y3 crates/yu-types/src/lib.rs c6587027612157c070a1b27b297a9f5aeec066422cf550eb78e3ec4828f0aa6b
Y3 crates/yu-solver/src/candidate_source.rs cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
Y3 crates/yu-solver/src/candidate_scheme.rs 2e64dc8781189b4da21c30f4d1b3208aaef48ca247cae55fb7e77e68b5857850
Y3 crates/yu-solver/src/candidate_call.rs e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479
Y3 tools/inference-playground/src/lib.rs a0769f77feac552304f0516b0742637f51660c0bb8bf9391d18ae0f9de5e2473
Y3 tools/inference-playground/src/runtime/program.rs 28748da0458da92b9d1190b250bbb84bdecc6643718eacbca95a04f5d6c9aa0d
Y3 tools/inference-playground/src/runtime/machine.rs 4fb918732047f61184bc8f89b829bde68a8d1e6649a24d02640ec14500ae0acd
```
