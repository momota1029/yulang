# Source/HIR selective-SCC search: authentic partial composition

Status: frozen, unreviewed research-only executable characterization. No R
counterexample, impossibility theorem, gate closure, or production authority.
Assigned baseline: `06f91e94fb86c369d020457c66953c42fd7bebc3`.
Producer and exclusive tracked write lease: `/root/source_hir_witness`, this note.
Main constructive theorem work belongs to the primary's prover lane.

## Objective, authority, and exact open premise

Construct the R state in the positive-tail composition note using actual source,
parser, HIR lowering, candidate collection, and the normal sequential action
schedule. No explicit calls to candidate_extrude, fresh_* allocation, restore,
constraint injection, or manufactured graph rows were used to construct the
states below. The debugger changes only the source bytes consumed by the existing
parser/session helper and then observes normal execution.

Authority is contextual attachment/admission design §§3.1–5: occurrence-owned
attachment grouping and member ordinals, scoped tails, level-selected bounds,
actual parent/copy provenance, exact contextual obligation transport, and
pairwise qualifying SCC intrusion. The primary's accepted language decisions
remain fixed; this work adds no semantic clause or source restriction.
Research-lab, design-authority, git-concurrency, agent-orchestration, testing,
and the yulang-proofs skill were read. The skill's constructive routing belongs
to the primary; this leaf did not delegate or claim prover execution.

Direct research inputs are the frozen owner-return note and positive-tail
composition note. The primary subsequently supplied the older-lower route:

```text
S + R; S - Allowance(v[T]); R - Allowance(w[X]); X -> S
positive incoming extrusion additionally gives C + R
```

The executable trace below constructs the first three keys and C + R. Its
precise remaining source premise is an admitted continuation from the retained
negative tail copy X, or its true scoped construction owner, to the recorded
original S. The original scoped name still denotes T, not X. A new annotation
with the same spelling is insufficient.

A complete R witness additionally needs owner-only qualification without any
other parent/copy merge lowering T, later capture/restoration on that unchanged
owner with existing positive lowers, an exact omitted required ordered fiber
pair, and failure of all subsequent ordinary/diagnostic rescue. None of these
last conclusions is claimed.

## Actual source and source formation

The main current-build program is:

```yulang
act E:
    our emit: () -> int
my left g = { my bridge (consume:(int -> [E, 'e] int) -> ['e] int) = { my cb x = E::emit(); my earlier = consume cb; my feed = g consume; consume }; bridge }
```

The helper at candidate_effect.rs:1441–1465 calls parse_file, requires no
structural recoveries, calls lower_module_with_local_source with empty imports,
collect_candidate_mode(hir,true,true), creates the session, and starts its
candidate graph. The host test then finds definition `left` and invokes
execute_candidate_source_root. Execution stops at :1879, after that complete
root schedule and before the host fixture's original expectations, explicit
synthetic effect contribution, manual capture, or freshening. This is a
successful root execution with zero solver errors, not a completed host test
or module publication run.

The owning HIR artifact is `effect-kernel/source.yu`; all occurrence numbers
below are relative to that single artifact. `bridge` is local slot 0,
`cb` slot 1, `earlier` slot 2, `feed` slot 3.
The formal consume parameter is candidate parameter 1, scoped by
AnnotationScope::Local(bridge's retained HirLocalId). Its annotation row begins
at byte 71. The nominal E operation signature begins at byte 21 and its lookup
is HIR occurrence 9. No independently reconstructed scope is substituted.

The primary first supplied only a tracked-note lease. It later explicitly
authorized an isolated Cargo build of the existing harness. The generated
directory is `/tmp/yulang-source-hir-selective-scc-20261010`; it is not a
checkpoint path. No tracked compiler/test file was edited by this worker.

## Complete admitted action order

Here `F index:occ/slot` is the emitted source Fact at that exact HIR occurrence
and local slot. This table preserves every executed action in order.

| Order | Actions |
| --- | --- |
| 1 | FormalAnnotation(parameter=1, occ=4) |
| 2 | F0:9/1, F1:9/2; Operation(occ=9,target=21,level=3) |
| 3 | F2:8/0, F3:8/1, F4:8/2, F5:8/3; Candidate0 |
| 4 | F6:6/0, F7:6/1; Lambda0; F8:6/20; Install(slot1,Component13,boundary2) |
| 5 | F9:11/1, F10:11/2, F11:12/1, F12:12/2; Local(slot1,occ12,value27,level3); Candidate1 |
| 6 | F13:10/20; Install(slot2,Component15,boundary2) |
| 7 | F14:14/1, F15:14/2, F16:15/1, F17:15/2; Candidate2 |
| 8 | Within Candidate2: incoming Allowance insertions on owners 40 and 41, tail40, Allowance3 |
| 9 | F18:13/20; Install(slot3,Component17,boundary2) |
| 10 | F19:16/1, F20:16/2; Candidate3 |
| 11 | F21:4/0, F22:4/1; Lambda1; F23:4/20; Install(slot0,Component7,boundary1) |
| 12 | F24:17/1, F25:17/2; Local(slot0,occ17,value5,level1) |
| 13 | Within that Local: restore Allowance5 on fresh53 with N=0; restore Allowance5 on fresh49 with N=0 |
| 14 | Candidate4; F26:2/0, F27:2/1; Lambda2; Link(occ2,Component1,target0) |

Candidate0 is E::emit(); Candidate1 is the first consume cb; Candidate2 is
g consume; Candidate3 is the inner block's final Group relation; Candidate4
is the enclosing block's final Group relation. Source planner entrypoints are
candidate_source.rs:229–300, :310–450, :549–573. Apply owns structural demand
and evaluation/invocation links in shadow_apply.rs:1340–1462. All parent records
below came from those actual admissions and ensuing level-selected extrusion.

## Live owner, lower, view, and parent identities

All row numbers in this section are actual EffectRow ordinals, not schematic
fresh allocations.

| Role | Row/view and physical state |
| --- | --- |
| Original tail T | row17, level2; original view0 tail17 |
| Negative checking owner S | row19, level2, -Allowance0; positive Support0, BottomPositive, and actual operation Support2 |
| Separate positive formal port P | row18, level2, +Support0, -row19; no physical Allowance on P |
| Negative owner copy R | row38, level1; parent record (38,19,Negative,target1) |
| Negative tail copy X | row42, level1; parent record (42,17,Negative,target1); view4 tail42 |
| Positive tail copy T' | row40, level1; parent record (40,17,Positive,target1); view3 tail40 |
| Positive incoming owner copy C | row41, level1; parent record (41,19,Positive,target1), -Allowance3 |
| Later fresh tail/owner | original17 local ->49; original19 local ->53; view5 tail49 |

The original annotation's Allowance0 is a real physical key on S. Actual
operation Support2 retains the E declaration and operation occurrence9 from
the independently freshened cb at occurrence12. Before inserting C's
Allowance3, the debugger observed C's exact positive vector:

```text
Support3, BottomPositive, Support2
```

C's direct positive lower R38 is also present. Support3 is the remapped
annotation Support0 with tail40; Support2 is the concrete operation lower
with no tail. This directly establishes timely copying of an actual positive
lower before the remapped incoming Allowance. It does not establish the
later selective return.

Representative physical keys and literal bound-fiber RelationIds observed
in the current-build final state are:

| Literal key | RelationId |
| --- | --- |
| (19,Negative,Allowance0) | 1 |
| (19,Positive,Support2) | 87 |
| (19,Positive,row38) | 108 |
| (17,Negative,row40) | 110 |
| (40,Negative,Allowance3) | 111 |
| (19,Negative,row41) | 112 |
| (41,Positive,row38) | 113 |
| (41,Positive,Support3) | 114 |
| (41,Positive,BottomPositive) | 115 |
| (41,Positive,Support2) | 116 |
| (41,Negative,Allowance3) | 117 |
| (17,Positive,row42) | 118 |

These are transported/derived relation identities. A relation's source cause
cannot be inferred from its numeric ID. The schedule above supplies the
actual formal/operation/call producers; the full dependency DAG for IDs1/87
was not separately inverted. Later origins at occurrence17/slot0 were
observed on transported relation113 and later C positive Support relations176
and185. No occurrence identity was inferred from nominal E spelling.

In the older-lower route, S19 + R38 and R38 - Allowance4[X42] are physical.
After the bridge lookup R38 also has Allowance5[X49]. Therefore this source
supplies the exact first three keys and C41 + R38. Both candidate X identities
fail the last return premise.

## Actual SCC tests and the missing fourth key

The debugger reads the physical Effect bounds and retained view tails and
computes reachability. Row -> Allowance/Support -> tail is compressed to a
row -> tail edge only for this reachability calculation. Effect constructors
cannot lead into Value rows, so Value Function adjacency cannot introduce
an omitted outward edge from these Effect rows. This calculation shares the
inspected candidate_intrusion.rs:382–493 graph definition; it independently
reads the emitted runtime state, but is not an independent oracle for language
meaning.

For the main program:

```text
C41 reaches {36,38,40,41,42,43,44,47,49,54,56}; does not reach S19
S19 reaches C41
T'40 reaches {40}; does not reach T17
T17 reaches T'40
```

Consequently neither recorded positive pair qualifies. Because C41 reaches
both X42 and X49, absence of S19 from C41's reachable set also excludes
X42 -> S19 and X49 -> S19 in this final graph. SCC generation is 0, dirty is
false, and every retained Effect representative entry is its own ordinal.
There was no intervening parent/copy merge to hide a prior successful return.

The scoped name map does not change from T17 to X42 during negative extrusion.
Calling consume again accesses its retained original formal interface and T17.
The absence of a source position identifying X42 is not a universal
impossibility invariant; it is the exact missing producer for this attempt.

## Additional source operations and discriminating outcomes

An initial program without the outer consume result ['e] row only constructed
negative copies of S and T; its prebuilt-binary provenance was unknown, so that
observation is exploratory. Adding the explicit singleton symbolic result
produced the genuine positive incoming pairs above in the current build.

The primary requested a real continuation through the existing scoped owner.
One additional normal call was tried after g consume:

```yulang
act E:
    our emit: () -> int
my left g = { my bridge (consume:(int -> [E, 'e] int) -> ['e] int) = { my cb x = E::emit(); my earlier = consume cb; my feed = g consume; my after = consume cb; consume }; bridge }
```

This reuses the same retained consume formal and scoped tail; it adds no new
'e annotation. New HIR allocation changes numeric row IDs between programs:
the analogous identities are S22, T20, R41, X45, C44, T'43.
The post-extrusion call is HIR occurrence16; its cb lookup is occurrence18.
The original annotation still has view0/tail20 at byte71.

Its physical continuation adds real outgoing invocation/block links from X45,
but still gives:

```text
C44 reaches {39,41,43,44,45,46,47,58,60,65,66,69}; excludes S22
T'43 reaches {43}; excludes T20
X45 and later fresh X60 exclude S22
```

The later bridge lookup at occurrence20 restores Allowance6 only on fresh
owners64 and60, both N=0. The complete root executes with zero errors. This
operation grows the actual continuation without producing the missing X -> S
edge. It is not an exhaustive source-family exclusion.

A separate probe tested the suggested older exposed Function-result port
receiving a later computation Allowance:

```yulang
act E
my left (g:int -> ['e] int) = { my checked:[E, 'x] int = g 1; g }
```

It parses, lowers, and executes without solver errors. g's exposed symbolic
positive result is row7 at level1. Apply negative extrusion creates invocation
copy10 at level1, with recorded pair (10,8,Negative,target1). The local
annotation (slot42, occurrence4, level2, boundary1) installs Allowance0
(tail11, level2) on copy10; original checking owner12 has row10 as a physical
positive lower. Result port7 has only upper row10 and no physical Allowance.
Thus this actual route does not justify moving the later registration onto
the exposed positive port. It tests a symbolic port, not every mixed
Support-bearing positive port.

Two preliminary ascription/unit spellings failed the helper's parser recovery
assertion. Their spellings were
`g():[E, 'e] int` and `g() as [E, 'e] int` in a unit-formal variant.
They supplied no HIR/runtime evidence. Their parse cause was not investigated
further; the valid local-annotation probe above replaces that attempt.

## Restoration products, whole-use replay, and rescue

For the main program's actual bridge use, capture labels S19 and T17 local
at boundary1; both freshen. C41, T'40, R38, and X42 are shared and retain
their identities. C41 is present in the captured row map but no Allowance key
from its older stopped row is reconstructed on C41.

The complete Allowance restoration trace contains exactly:

```text
owner53 - Allowance5, N=0, incoming occurrence17
owner49 - Allowance5, N=0, incoming occurrence17
```

Each saved-count loop has zero iterations and emits no incoming-use Cartesian
product. This is not a missed required product on unchanged C41: the required
capture/restoration premise for that owner has not occurred. No exact omitted
ordered fiber pair omega, source cause, or observable consequence was found.

All later restores and the final Local Value link ran before the final root
stop. Subsequent physical C41 positive Support5/Support6 and their incoming
occurrence17 lineage demonstrate ordinary propagation into the shared anchor.
Repeated captures/fibers were not cut off by the observer: the entire action
schedule was allowed to finish. The extended repeated-call program likewise
finishes every later action.

Rescue audit at the intended scope:

- Qualifying merge replay never runs in the main trace: generation stays0.
- Ordinary bound admission and later positive restoration are permitted to
  replay the current opposite bounds; none was suppressed by the debugger.
- Both actual Allowance restore counts are0, so no nested callback/SCC drain
  from those loops can reorder their saved opposite frontier.
- The final lookup Value link and source root Link execute.
- Value/Effect diagnostic deltas report zero solver errors. No named missing
  obligation exists for which a diagnostic rescue failure could be tested.

The consumer contracts remain candidate_extrusion.rs:599–641,:646–751,
candidate_scheme.rs:998–1032,:1127–1135, candidate_context's incoming-use
Cartesian replay, candidate_intrusion.rs:549–603, and
candidate_effect.rs:524–580/lib.rs:12083–12099. This audit does not prove
universal rescue coverage or full restoration correctness R.

## Complete restoration and literal fiber-product inventory

A final observation pass on the same current-build main source recorded every
candidate_restore_bound call, including Value and positive restores. It
reached the same post-root breakpoint. V/E prefixes distinguish Value/Effect
rows; function Term indices are local to this arena.

| Restore | Incoming occurrence | Owner | Physical bound | Saved N |
| --- | --- | --- | --- | --- |
| 1 | 12 | V20 | +PositiveFunction(Term#299) | 0 |
| 2 | 12 | V21 | +IntPositive | 0 |
| 3 | 12 | E26 | +BottomPositive | 0 |
| 4 | 12 | E26 | +Support(2) | 0 |
| 5 | 12 | E27 | -EffectRow(26) | 0 |
| 6 | 17 | V29 | +PositiveFunction(Term#363) | 0 |
| 7 | 17 | V30 | +PositiveFunction(Term#370) | 0 |
| 8 | 17 | E47 | +EffectRow(44) | 0 |
| 9 | 17 | E47 | +EffectRow(36) | 0 |
| 10 | 17 | E47 | +BottomPositive | 0 |
| 11 | 17 | E48 | -EffectRow(47) | 0 |
| 12 | 17 | E53 | -Allowance(5) | 0 |
| 13 | 17 | E49 | -Allowance(5) | 0 |
| 14 | 17 | E49 | +EffectRow(42) | 1 |
| 15 | 17 | E49 | -EffectRow(54) | 1 |
| 16 | 17 | E49 | -EffectRow(40) | 1 |
| 17 | 17 | E50 | +EffectRow(39) | 0 |
| 18 | 17 | E50 | +BottomPositive | 0 |
| 19 | 17 | E51 | -EffectRow(53) | 0 |
| 20 | 17 | E51 | +Support(5) | 1 |
| 21 | 17 | E52 | -EffectRow(55) | 0 |
| 22 | 17 | E52 | -EffectRow(37) | 0 |
| 23 | 17 | E53 | +EffectRow(38) | 1 |
| 24 | 17 | E53 | -EffectRow(41) | 2 |
| 25 | 17 | E53 | +Support(5) | 2 |
| 26 | 17 | E53 | +BottomPositive | 2 |
| 27 | 17 | E53 | +Support(6) | 2 |
| 28 | 17 | E54 | +EffectRow(43) | 0 |
| 29 | 17 | E54 | -EffectRow(56) | 1 |
| 30 | 17 | E55 | -EffectRow(57) | 0 |
| 31 | 17 | E56 | +EffectRow(44) | 0 |
| 32 | 17 | E56 | +EffectRow(36) | 0 |
| 33 | 17 | E56 | -EffectRow(47) | 2 |
| 34 | 17 | E56 | +BottomPositive | 1 |
| 35 | 17 | E57 | -EffectRow(58) | 0 |
| 36 | 17 | E58 | -EffectRow(53) | 0 |
| 37 | 17 | E58 | +BottomPositive | 1 |
| 38 | 17 | E58 | +Support(6) | 1 |

The corresponding incoming-use literal Cartesian products are listed in their
actual invocation order. Each table entry gives the exact RelationId fibers
selected at that call. There were no intervening merges or rollback; the
bound-entry decoder collects exact literal-key entries in newest-first order.
It does not independently establish that these source transitions are correct.
Each displayed fiber is a singleton; the per-callback products therefore
contain one ordered pair. Duplicate pair168/175 reflects two real restore
calls and is not silently deduplicated here.

| Product | During restore | Lower × upper fibers | Ordered pair list |
| --- | --- | --- | --- |
| 1 | 14 | [159] × [158] | [(159, 158)] |
| 2 | 15 | [159] × [161] | [(159, 161)] |
| 3 | 16 | [159] × [163] | [(159, 163)] |
| 4 | 20 | [167] × [166] | [(167, 166)] |
| 5 | 23 | [173] × [157] | [(173, 157)] |
| 6 | 24 | [173] × [175] | [(173, 175)] |
| 7 | 24 | [168] × [175] | [(168, 175)] |
| 8 | 25 | [168] × [175] | [(168, 175)] |
| 9 | 25 | [168] × [157] | [(168, 157)] |
| 10 | 26 | [181] × [175] | [(181, 175)] |
| 11 | 26 | [181] × [157] | [(181, 157)] |
| 12 | 27 | [184] × [175] | [(184, 175)] |
| 13 | 27 | [184] × [157] | [(184, 157)] |
| 14 | 29 | [190] × [191] | [(190, 191)] |
| 15 | 33 | [194] × [196] | [(194, 196)] |
| 16 | 33 | [195] × [196] | [(195, 196)] |
| 17 | 34 | [197] × [196] | [(197, 196)] |
| 18 | 37 | [200] × [199] | [(200, 199)] |
| 19 | 38 | [201] × [199] | [(201, 199)] |

The initial Allowance restores have N=0, but later positive restoration on
fresh owners does replay those Allowances. This distinction matters: an empty
initial Allowance product does not imply an empty full use. No restore in this
inventory targets unchanged C41 or original S19; all nonzero products are
Effect products, with the retained literal heads shown in the observer script.
No exact required fiber outside these emitted products was established.

One initial ProductTrace breakpoint also matched the publish closure where
lower_input is unavailable and stopped the observer early. The final
instrumentation skips that closure location, records every caller product,
and allows every callback to run to completion.

## Reproducibility and coverage limits

The isolated current build command was:

```bash
timeout 180s env CARGO_TARGET_DIR=/tmp/yulang-source-hir-selective-scc-20261010 RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests::formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber --offline --jobs=1 --no-run
```

It completed in 48.36s without reported warnings. A later identical command
with timeout60s returned in0.04s with no compilation, confirming Cargo considers
the current sources fresh for that isolated artifact. The harness binary hash
is `7aee4053118d02e626d70695433018c356105e8e7663e3f9776b5d922c4a4ec3`.

The following reproduces the main current-build source injection and complete
action/incoming/restoration/SCC observation without a scratch source file:

```bash
python3 - <<'PY'
import json, subprocess
source = "act E:\n    our emit: () -> int\nmy left g = { my bridge (consume:(int -> [E, 'e] int) -> ['e] int) = { my cb x = E::emit(); my earlier = consume cb; my feed = g consume; consume }; bridge }"
binary = "/tmp/yulang-source-hir-selective-scc-20261010/debug/deps/yu_solver-12ea9c1c0f03380a"
trace = "import gdb\ndef vec(v, typ=None):\n p=v['buf']['inner']['ptr']['pointer']['pointer'].cast(v.type.template_argument(0).pointer())\n return [p[i] for i in range(int(v['len']))]\ndef variant(v):\n names=[f.name for f in v.type.fields() if f.name]\n return names[-1],v[names[-1]]\nclass ActionTrace(gdb.Breakpoint):\n def stop(self):\n  a=gdb.parse_and_eval('action').dereference(); k,x=variant(a)\n  desc=[]\n  for f in x.type.fields():\n   n=f.name\n   if n=='occurrence': desc.append('occ='+str(x[n]['ordinal']))\n   elif n in ('slot','level','boundary','value','target','parameter','endpoint','initializer','computation_effect','__0'): desc.append(n+'='+str(x[n]))\n  if k=='Fact':\n   s=gdb.parse_and_eval('self').dereference();fact=vec(s['batch']['occurrences'])[int(x['__0'])]\n   desc.append('occ='+str(fact['id']['occurrence']['ordinal'])+'/'+str(fact['id']['local_slot']))\n  print('ACTION',k,' '.join(desc))\n  return False\nclass RestoreTrace(gdb.Breakpoint):\n def stop(self):\n  b=gdb.parse_and_eval('bound')\n  print('RESTORE_ALL',gdb.parse_and_eval('owner'),gdb.parse_and_eval('p'),b,'N',gdb.parse_and_eval('count'),'occ',gdb.parse_and_eval('occurrence').dereference()['occurrence']['ordinal'])\n  return False\nActionTrace('crates/yu-solver/src/candidate_source.rs:551',internal=True)\nRestoreTrace('crates/yu-solver/src/candidate_extrusion.rs:615',internal=True)\n\nclass ProductTrace(gdb.Breakpoint):\n def stop(self):\n  try: lo=gdb.parse_and_eval('lower_input');hi=gdb.parse_and_eval('upper_input')\n  except gdb.error: return False\n  s=gdb.parse_and_eval('self').dereference();ctx=s['candidate_graph']['Some']['__0']['intrusion']['effect_algebra']['context']\n  es=vec(ctx['bound_keys'])\n  l=[int(e['__1']['__0']) for e in reversed(es) if str(e['__0'])==str(lo)]\n  u=[int(e['__1']['__0']) for e in reversed(es) if str(e['__0'])==str(hi)]\n  print('PRODUCT',str(lo),str(hi),'FIBERS',l,u,'PAIRS',[(a,b) for a in l for b in u])\n  return False\nProductTrace('crates/yu-solver/src/candidate_extrusion.rs:635',internal=True)\n\nclass IncomingTrace(gdb.Breakpoint):\n def stop(self):\n  src=gdb.parse_and_eval('source'); print('INCOMING_OWNER',src,'TAIL',gdb.parse_and_eval('tail'),'ALLOW',gdb.parse_and_eval('allowance'))\n  s=gdb.parse_and_eval('self');i=int(str(src).split('EffectRow(')[1].split(')')[0]);b=vec(s['effect_bounds'])[i]\n  print('PRE_ALLOW_LOWER',*[str(x) for x in vec(b['exact_non_variable_lowers'])])\n  return False\nIncomingTrace('crates/yu-solver/src/candidate_extrusion.rs:303',internal=True)\n"
inspect = "s=gdb.parse_and_eval('session')\nst=s['candidate_graph']['Some']['__0']\nprint('END_ERRORS',s['errors']['len'],'GEN',st['intrusion']['generation'],'DIRTY',st['intrusion']['dirty'])\nprint('REPS',*[int(x) for x in vec(st['intrusion']['effects'])])\nfor r in vec(st['local_routes']):\n print('LOCAL_ROUTE',r['slot'],'OCC',r['occurrence']['ordinal'],'ROWS',*[str(x) for x in vec(r['rows'])])\n\nimport re\nal=st['intrusion']['effect_algebra']\nviews=vec(al['views']);bounds=vec(s['effect_bounds'])\nadj={}\nfor i,b in enumerate(bounds):\n adj[i]=set(int(x) for k in ('direct_lower_rows','direct_upper_rows') for x in vec(b[k]))\n for k in ('exact_non_variable_lowers','exact_non_variable_uppers'):\n  for x in vec(b[k]):\n   m=re.search(r'(?:Allowance|Support)\\((\\d+)\\)',str(x))\n   if m:\n    tail=views[int(m.group(1))]['tail']\n    if 'Some' in str(tail):adj[i].add(int(tail['Some']['__0']))\ndef reach(i):\n found=set();todo=[i]\n while todo:\n  x=todo.pop()\n  if x not in found: found.add(x);todo.extend(adj.get(x,()))\n return found\nfor i,j in ((41,19),(40,17)):\n print('SCC_TEST',i,j,j in reach(i),i in reach(j),'FROMCOPY',sorted(reach(i)))\nctx=al['context'];rids=set()\nfor e in vec(ctx['bound_keys']):\n if any('EffectRow('+str(i)+')' in str(e['__0']) for i in (17,19,40,41)):\n  print('FIBER',e['__0'],'RID',e['__1']);rids.add(int(e['__1']['__0']))\nfor o in vec(ctx['origins']):\n if int(o['relation']['__0']) in rids: print('ORIGIN',o['relation'],'OCC',o['occurrence']['occurrence']['ordinal'],'SLOT',o['occurrence']['local_slot'])\nfor r in vec(st['local_routes']):\n if int(r['slot'])==0:\n  for a,b in zip(vec(r['graph']['rows']),vec(r['rows'])): print('ROWMAP',a['key'],a['local'],'->',b)\n"
commands = [
    "set pagination off", "set debuginfod enabled off", "set print elements 80",
    "break yu_solver::candidate_effect::tests::make_session",
    "run candidate_effect::tests::formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber --exact --test-threads=1",
    "set language c", "set $probe = (char*)malloc(2048)",
    "call (void)memcpy($probe, " + json.dumps(source) + ", " + str(len(source)) + ")",
    "set text.data_ptr = (unsigned char*)$probe", "set text.length = " + str(len(source)),
    "set $rdi = $probe", "set $rsi = " + str(len(source)), "set language rust",
    "break crates/yu-solver/src/candidate_effect.rs:1879",
    "python exec(" + json.dumps(trace) + ")", "continue",
    "python exec(" + json.dumps(inspect) + ")",
]
args = ["timeout", "40s", "gdb", "-q", "-nx", "-batch"]
for command in commands:
    args += ["-ex", command]
subprocess.run(args + [binary], check=True, timeout=45)

PY
```

The debugger breakpoint is after the helper's parameter registers have already
been prepared for Arc::from(text). Updating the DWARF text variable alone
does not change that call; rdi/rsi must also be changed. An early bootstrap
attempt changed only the debug variable and therefore still ran the host's
original text. That attempt was rejected as source evidence. The current
source's different HIR inventory, action sequence, operation occurrence, and
61 Effect bound slots corroborate that the parser consumed the replacement.

An earlier Vec decode used an incomplete named GDB type and failed; the
final decoder takes each Vec's concrete element template argument. One
incoming-owner trace attempted to dereference an already direct closure self
value and stopped early; the corrected current trace completed. These failed
debugger observations were not counted as source witnesses.

Coverage is three valid current-build source programs: main symbolic-result
composition, one post-extrusion repeated call, and one older-result
local-check probe. It is not source enumeration, and there are no random seeds,
exhaustive ranges, semantic mutations, rollback/retry experiments, runtime
providers, or complete module publication checks. Initial prebuilt runs are
not current-baseline conformance evidence.

Resource envelope was one jobs=1 offline Cargo build, one cached freshness
check, and sequential GDB pilots, each bounded by timeout30s or40s. No parallel
build/test wave or broad suite ran. The measured decisive current GDB run used
0.72s elapsed, 1.23s user, 0.13s system, and332712KiB peak RSS, including debugger
and traced harness. Aggregate CPU/peak RSS for the cold build and all pilots
were not measured. The isolated target occupies 697MiB.

The final focused existing host test passed: 1 passed, 615 filtered, test
runtime 0.05s, cached compilation 0.21s, command elapsed approximately 0.235s:

```sh
timeout 60s env CARGO_TARGET_DIR=/tmp/yulang-source-hir-selective-scc-20261010 RUSTC_WRAPPER= cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests::formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber --offline --jobs=1 -- --exact --test-threads=1
```

That test checks the original fixture and its manual follow-up operations. It
is harness-health evidence; the injected-source experiments stop at the
post-root breakpoint and do not inherit that test's semantic assertions.

## Dependency snapshot and honest promotion boundary

Initial observed HEAD matched the assigned baseline
`06f91e94fb86c369d020457c66953c42fd7bebc3`. After these traces the primary
integrated its code, records, and proof checkpoint at
`f7c9202e0cefbdab31a63796eafd319252bded1d`. The assignment baseline remains
pinned; no constructor dependency change was observed.
Constructor and graph dependencies remained at:

```text
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0  candidate_source.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  candidate_effect.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  candidate_intrusion.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11  candidate_scheme.rs
6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6  shadow_apply.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  lib.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  yu-hir/module/local_source.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  yu-hir/module/source_annotation.rs
a3f39b574e343b2065897e6df3b04ccf525a31df5fea1ed69ecc0bf07611e41a  Cargo.lock
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  governing contextual attachment design
4243139aa2d00cffb5fe1e767786e391a88bfa8b9aa64f07c21a59c380ba5922  hir-owner-scc-return-path note
6e8a41bc27e0570c916cf49fa4e4a916b6bb6059ad8b0c32627a2d33a0cfbf93  positive-tail-source-composition-proof note
```

The primary-owned candidate_context.rs diff was present before work and was
left untouched. It changed during inspection from
`9d8a717407c711a6ffbc8734e5c4bceb609893ff691a8778737177da2c96cc0c`
to `3b219b51ed8aba6ffc85675fd1d500b901a6f63b31325a85a586d688eee3515a`;
its initial-baseline blob hash was
`c7719e0e8dc8fa1040b89d096e14d0794e261385bed4bdf6b50bd81befc58866`.
candidate_context_tests.rs also changed concurrently: initial-baseline
`5de97c959f4d6e181c07614708de4e4fe50eb9e90403eec5e353254f77eec768`
to live `2635a036a520001ecf6387ee8e1edabcb463e2f1f8d82ab1482797c24bb37f30`.
Their modification times precede the isolated binary, and the cached Cargo
freshness check ran after recording their current hashes. Thus execution is
associated with the current shared-source combination, not the pristine HEAD
blob combination. The primary subsequently integrated that separate diff at the checkpoint
above; this leaf does not independently certify it.

Unverified: the missing X -> S source producer; mixed Support-bearing P later
registration in all other shapes; all parent-pair alternatives lowering T;
a qualifying selective SCC and later unchanged-owner restore; exact omitted
fiber/rescue failure; full dependency-DAG source inversion; module capture/
publication and actual provider scheduling; rollback/retry; universal source
reachability or impossibility; independent mathematical review. Requested and
observed model/effort metadata are unknown for this runtime. No independent
review of this output is claimed.

Recommended next action: use this source prefix as the constructive input
for a narrowly assigned source-owner proof of the missing X -> S admission,
including the negative copy's original-tail scope and all parent pairs; avoid
another probe that only adds a freshly named tail or another ordinary
consume/cb call.

## Commit packet

Exact leased checkpoint path:
`notes/progress/2026-10-10-source-hir-selective-scc-witness.md`.
Baseline: `06f91e94fb86c369d020457c66953c42fd7bebc3`.
Changed dependency hashes: primary-owned candidate_context.rs and
candidate_context_tests.rs as recorded above; none changed by this worker.
Generated authorized build output: `/tmp/yulang-source-hir-selective-scc-20261010`,
excluded from Git. Review status: frozen, unreviewed research-only executable
characterization and precise blocker. Checks run: static owning-source reads,
dependency hashes/read-only Git status/HEAD/blob inspection, isolated focused
no-run build, cached freshness check, focused existing host test (1 passed,
615 filtered), bounded GDB source-root traces, physical Effect reachability
calculation and full restoration-input/product inventory. No tracked compiler/test/expected-output edit,
Git mutation, shared record edit, or child launch.

Proposed checkpoint message:
`research: construct real source prefix for selective owner restoration`.

Shared-record deltas intentionally left for primary/curator: replace the
missing-positive-lower/positive-copy premise for this exact prefix with
observed source evidence; keep the missing X -> S return, later same-owner
restoration, exact omitted fiber, and universal rescue gates open. Record the
normal Apply invocation-copy separation from the older positive symbolic
port; do not promote it to a global mixed-port invariant or close R.
