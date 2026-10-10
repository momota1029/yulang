# Positive Function-port source route: bounded search

Date: 2026-10-10
Status: frozen, unreviewed research-only executable characterization and conditional source tracing. Restoration R remains OPEN; no source counterexample, impossibility theorem, gate closure, or production authority.
Baseline supplied by primary: `09ea300c3`, branch `research/simple-sub-intrusion`.
Producer: `/root/positive_port_source_witness`, research-only leaf; no delegation or Git operations.
Exclusive tracked output lease: this note only.

## Question and result

Can normal parsed/lowered source register a physical Allowance on an already
positive Function port P, expose its exact positive incoming-incidence copy C,
and make C reach original owner P while the corresponding tail copy does not
reach its original tail, at one qualifying snapshot?

Eight focused sources parse/lower and execute the complete normal root action
schedule with zero solver errors. None yields the requested selective positive
owner return. The final snapshot in every program has no returning positive
Effect parent/copy pair. Variant 3 has one negative Effect pair merge; it is
not the requested positive owner pair. This bounded failure is not a global
source exclusion, and final reachability is not a trace of every intermediate
qualification snapshot.

Two distinct results sharpen the surviving producer seam:

1. An authentic **symbolic positive port** does receive a physical self-tail
   Allowance, and positive traversal and incoming incidence select its same
   positive copy. The relevant original owner equals the original tail, so
   its owner and tail parent pairs coincide. That incidence cannot support
   selective owner intrusion, regardless of whether a later return exists.
2. A deeper formal checking port initially appears to allow an older positive
   callback port P to receive an Allowance with a distinct younger tail.
   The actual Value demand is negatively extruded to the older callback's
   level first. The physical Allowance reaches checking/invocation copies;
   the original positive callback result port remains without an Allowance.
   This is the concrete source-level obstruction for these variants, not
   permission to identify the copied checking receiver with original P.

Governing authority: contextual attachment/admission design §§3.1–5.
Occurrence/member identity, annotation scopes, composed polarity, level-selected
orientation, exact operation-local copy keys and recorded parent pairs retain
existing meanings. No semantics, source restriction, annotation guard, carrier,
test expectation, compiler implementation or shared task/theory record changes.
This is complementary source research; the primary's constructive proof lane
and independent review duties remain separate. Artifact bookkeeping is M0;
no reviewers were assigned to this producer and no self-certification is claimed.

## Authentic positive exposure with a self-tail incidence

Variant 4 provides the smallest directly observed forming-initializer prefix:

```yulang
act E
my left g = { my bridge (consume:(int -> [E, 'e] int) -> ['e] int) = { my feed = g bridge; consume }; bridge }
```

The helper parses the replacement source without structural recovery, lowers
with empty semantic imports, collects candidate mode, starts the graph, and the
host invokes `execute_candidate_source_root(left)`. Debugger execution stops
immediately after that complete root schedule, before the host fixture's
original assertions or synthetic allocations. It is root execution evidence,
not a full module-publication or host-test result. Artifact identity is
`effect-kernel/source.yu`; scopes are retained real local identities, not
identifications from equal spelling.

The observed action prefix is FormalAnnotation(parameter 1, occurrence 4);
Facts at occurrences 7 and 8; recursive open-initializer Link(occurrence 8,
Component 7, target 17); Candidate0 for `g bridge`; feed Install(slot1,
boundary2); Facts at occurrence9 and Candidate1 for the inner final Group;
Facts occurrence4 slots0/1 and Lambda0. That Lambda admission/replay performs
the observed incoming insertions on rows28 and29. Bridge Install(slot0,
boundary1), bridge Local use(occurrence10, level1), Candidate2, root Lambda1,
and root Link(occurrence2,target0) complete afterward.

| Role | Actual identity and physical facts |
| --- | --- |
| Symbolic result port P and original tail T | EffectRow10, level2; outer formal result `['e]` is the shared scoped row in both polarities; physical `-Allowance0`, whose tail is row10. |
| Mixed positive paired port | row11, level2; `+Support0`, upper rows12 and20; **no physical Allowance**. |
| Mixed negative checking owner | row12, level2; `-Allowance0`, `+Support0`; positive owner copy29 and negative structural copy26 are distinct. |
| View occurrence | original view0, source row position byte46, tail10; remapped view1 same original position, tail28. |
| Positive P/T copy C/T' | row28, level1; actual retained parent `(28,10,Positive,target1)`; incoming insertion `row28 - Allowance1`, tail28. |
| Distinct checking-owner incidence copy | row29, level1; actual retained parent `(29,12,Positive,target1)`; incoming `-Allowance1`, tail28. |
| Negative tail/checking copies | `(22,10,Negative,target1)`, `(26,12,Negative,target1)`; view2 tail22. |

The paired constructor uses exact row10 for the outer symbolic result port;
the Lambda body returns the Parameter endpoint. Its positive formal Function
lower contains that positive result port. When this lower is traversed
positively during the actual Lambda replay, the copied result uses
`Key(row10,Positive,1)`. Incoming incidence uses that same key. Exact structural
copy identity here follows the inspected constructor/traversal and the observed
parent/incoming events; the debugger did not separately serialize the rebuilt
Function term. It must not be confused with the mixed positive port row11.

The final canonical forest is unchanged (generation0, dirty=false). The
physical graph reachability calculation, compressing row→view→tail edges,
yields on that same final snapshot:

```text
C/T'28 reaches {22,28,33}; does not reach P/T10.
P/T10 reaches C/T'28.
C29 reaches {22,26,28,29,33}; does not reach owner12.
owner12 reaches C29.
```

The symbolic owner pair `(28,10)` is literally also its tail pair `(28,10)`.
A qualifying owner return through this self-tail incidence would qualify the
same pair as a tail return. For distinct owner12, its actual positive incidence
copy29 is still distinct from negative structural copy26, preserving the prior
negative-S polarity obstacle. Mere positive Support on owner12 does not make
its negative structural occurrence a positive occurrence.

The prior formal-incidence unit test's assertion that some Allowance owner
also has Support is therefore not evidence that mixed positive paired port P
has an Allowance: these actual source constructors give that Support-bearing
owner to the negative checking port, while the second incidence owner is the
shared symbolic tail. No test was changed or run to alter that interpretation.

## Distinct-tail registration attempt and actual level collapse

Variant 2 makes the intended older callback row and deeper checking row real:

```yulang
act E
my left g = { my bridge (cb:int -> ['e] int) = { my consumer (consume:(int -> [E, 'x] int) -> ['x] int) = { my earlier = consume cb; cb }; my feed = g consumer; consumer }; bridge }
```

FormalAnnotation(parameter1, occurrence4) allocates the bridge callback result
P=row16 at level2. FormalAnnotation(parameter2, occurrence6) allocates the
consumer scoped tail X=row18 at level3, positive mixed port19, and negative
checking owner20, with view0/tail18 at source position byte83. The attempted
`consume cb` is Candidate0, preceded by Names at occurrences9 and10.

Actual callback Value demand extrusion creates negative effect pairs
`(26,20,Negative,target2)` and `(27,18,Negative,target2)`. Rows26/27 receive
physical `Allowance1`, tail27. Original checking owner20 retains `Allowance0`,
tail18, and has row26 as a positive lower. Original cb result row16 retains no
physical Allowance. The cb result port row16 points to checking copy26;
argument-effect row15 and result row16 are distinct real Function ports. A
claim that the original result P16 received the registration would silently
replace either port identity or extrusion polarity.

Later local uses freshen consumer-owned rows and actual `g consumer`
positive extrusion creates `(50,27,Positive,target1)` and
`(51,26,Positive,target1)`, with remapped `Allowance3` tail50. It also creates
the positive original callback result copy49 from row16 and the negative
argument-effect copy48 from row15. Copy49 has no physical Allowance, so it
cannot be identified with actual incoming owner51. The exact stored pairs
are used; names such as "callback copy" do not license replacing one with another.

Final reachability for this actual incoming owner51/tail50 is:

```text
51 reaches {45,47,50,51,52,53,54,55,73,75,80,81,84,85,86,88,89}; excludes26.
50 reaches {45,47,50,52,53,54,55,73,75,80,81,84,85,86,88,89}; excludes27.
26 reaches51; 27 reaches50.
```

Those tests share one final snapshot (zero errors, generation0, dirty=false).
They fail the owner return and tail return together; they do not form R.
The original scoped X18 and original callback result P16 remain different
scope/row identities, and X18 is not the copied X27 merely because the view
retains source position byte83.

Owning source seam: Function ports reverse arguments/preserve results in
`candidate_formal_pair` (`candidate_effect.rs:908–935`); actual Value comparison
extrudes a structured negative upper to the receiver Value row's level
(`lib.rs:11958–11973`) before Function children compare. `candidate_apply_effect`
then selects physical ownership from canonical levels
(`candidate_extrusion.rs:726–751`). An isolated Effect-level inequality with
P older than S omits that preceding real Value extrusion. The missing producer
is a normal action that compares an already positive exposed P to a distinct
younger Allowance receiver **without first replacing that receiver at P's
Value boundary**, or a different admitted/reconstructed path placing the
Allowance directly on the exact original P. These variants establish neither
such a producer nor its universal absence.

## Complete bounded source envelope

Every authored program below is an attempted source, not an expected type or
semantic fixture. Variant1 was executed twice because the initial observer's
representative-array access assumed every live row already had a forest entry.
That observer failed after successful root execution; its results were not
used. The corrected observer treats absent forest entries as identity rows.
There are eight distinct sources and nine GDB runs, with no ninth variant.

| Variant | Method | Effect parent pairs / positive pairs | Final generation | Result |
| --- | --- | --- | --- | --- |
| 1 | Pass installed mixed-formal bridge to older g | 14 / 7 | 0 | no positive return |
| 2 | Deeper mixed-formal consumer and older cb | 23 / 11 | 0 | original cb result has no Allowance; no positive return |
| 3 | Pass forming recursive consumer before installation | 33 / 16 | 1 | only negative pair61→51 merged; no positive return |
| 4 | Pass forming recursive bridge | 14 / 7 | 0 | positive symbolic self-tail incidence; no positive return |
| 5 | Variant4 with shared Value variable g:`'a -> 'a` | 14 / 7 | 0 | no positive return |
| 6 | Add real before/after calls to mixed formal | 33 / 11 | 0 | no positive return |
| 7 | Repeat older-g use of consumer | 41 / 20 | 0 | no positive return |
| 8 | Share g's Value variable and return feed | 23 / 11 | 0 | no positive return |

### Variant 1

```yulang
act E
my left g = { my bridge (consume:(int -> [E, 'e] int) -> ['e] int) = consume; my feed = g bridge; bridge }
```

### Variant 2

```yulang
act E
my left g = { my bridge (cb:int -> ['e] int) = { my consumer (consume:(int -> [E, 'x] int) -> ['x] int) = { my earlier = consume cb; cb }; my feed = g consumer; consumer }; bridge }
```

### Variant 3

```yulang
act E
my left g = { my bridge (cb:int -> ['e] int) = { my consumer (consume:(int -> [E, 'x] int) -> ['x] int) = { my earlier = consume cb; my feed = g consumer; cb }; consumer }; bridge }
```

### Variant 4

```yulang
act E
my left g = { my bridge (consume:(int -> [E, 'e] int) -> ['e] int) = { my feed = g bridge; consume }; bridge }
```

### Variant 5

```yulang
act E
my left (g:'a -> 'a) = { my bridge (consume:(int -> [E, 'e] int) -> ['e] int) = { my feed = g bridge; consume }; bridge }
```

### Variant 6

```yulang
act E
my left g = { my bridge (consume:(int -> [E, 'e] int) -> ['e] int) = { my cb x = 1; my earlier = consume cb; my feed = g bridge; my after = consume cb; consume }; bridge }
```

### Variant 7

```yulang
act E
my left g = { my bridge (cb:int -> ['e] int) = { my consumer (consume:(int -> [E, 'x] int) -> ['x] int) = { my earlier = consume cb; cb }; my feed = g consumer; my again = g consumer; consumer }; bridge }
```

### Variant 8

```yulang
act E
my left (g:'a -> 'a) = { my bridge (cb:int -> ['e] int) = { my consumer (consume:(int -> [E, 'x] int) -> ['x] int) = { my earlier = consume cb; cb }; my feed = g consumer; feed }; bridge }
```

## Checks, provenance, resources and exclusions

The primary confirmed the current HEAD compiler/HIR hashes equal the prior
witness's post-filter-repair source combination, with no later compiler changes.
This leaf independently compared every listed solver/HIR/lockfile digest with
that witness, including current context and context tests, and compared the
existing binary digest. A scan of 247 `.rs`/`.toml` files under solver/HIR/syntax
found no source newer than the binary. The prior witness records its isolated
build and a cached Cargo freshness check for exactly these bytes. That is the
build provenance used here; no Cargo command or new build was launched, and
mtime equality alone was not used as the source certificate. Baseline Git blob
verification belongs to the primary; this leaf performed no Git operation.

Exact executable commands were `python3
/tmp/yulang-positive-port-source-route-20261010/run.py v1` twice, then the same
command with `v2` through `v8`, sequentially. Each launches the existing harness
under `timeout 45s gdb -q -nx -batch`, sets the replacement source slice **and**
rdi/rsi before Arc construction, then observes the normal host root schedule.
The complete executed runner is retained below so source injection, breakpoints,
reachability and stop location do not depend on a hand-written graph fixture.
A proposed premerge snapshot breakpoint at intrusion line493 never fired in
these runs; only the end-root snapshot is used. No intermediate selective-SCC
snapshot or restored-fiber failure is claimed.

Static checks: `cat`, bounded `sed`, `rg`, source hash comparison, source-vs-binary
mtime audit, final runtime pair/row inventory parsing, and final dependency
recheck. No compiler/test/spec/fixture/shared-record edit, synthetic solver
call, fresh-row injection, ordinary constraint injection, test execution beyond
the stopped harness prefix, external oracle, full suite, build, performance
measurement, Git mutation, or delegation. The debugger changes only source
input and reads state. The physical SCC calculation shares the candidate graph
edge definition, so it is emitted-state evidence rather than an independent
semantic oracle.

Resource envelope: one probe at a time, one CPU affinity shared by GDB and its
inferior; 1.5GiB address-space limit, observed peak RSS at most335632KiB;
85s CPU limit and45s process timeout per run (Python timeout50s). Nine GDB runs,
eight valid final inventories; no timeout or resource kill. Recorded wall
seconds/peak KiB are respectively: initial v1 observer failure1.470/332736;
corrected v1 1.321/333420; v2 1.419/335632; v3 1.419/334260;
v4 1.319/334484; v5 1.373/333188; v6 1.369/333708;
v7 1.470/334220; v8 1.422/335564. GDB plus inferior and the Python controller
are multiple OS processes; "one probe" is not a claim of one OS process.
Performance timing samples: zero; these resource observations characterize
bounded correctness probes only.

Unverified: every ordinary source/provider order, successful intermediate
qualification snapshots, full rebuilt Function serialization, module capture/
publication, transactional retry, a genuine selective positive owner return,
later same-owner Allowance restoration with surviving lowers, within-loop
mutation, exact omitted ordered fiber omega, and all subsequent Value/Effect
replay and diagnostic rescue. No impossibility or defect follows from the
bounded absence above.

Surviving seam: a physical distinct-tail Allowance on the **exact** positive
exposed port P before the positive operation, positive structural/incidence
selection of the same C, and a real post-copy return to P independent of the
original Allowance tail pair. Existing mixed positive mate P, negative checking
S, negative copy D, and positive incidence C remain distinct. A self-tail
symbolic port supplies the first two premises only with owner=tail, which cannot
supply selective intrusion. The Value-demand level collapse excludes the
identified deeper-consumer attempt only. No third reconstruction relation or
source restriction is proposed to simplify this remaining proof obligation.

## Reproducible executed runner

Write the eight programs to `v1.yu` … `v8.yu` under the unique scratch directory
and run this script with the variant basename. The existing binary has the
pinned digest in the manifest. Scratch is excluded from the tracked checkpoint.

```python
from pathlib import Path
import subprocess,json,sys,resource,os,time
base=Path('/tmp/yulang-positive-port-source-route-20261010')
source=(base/(sys.argv[1]+'.yu')).read_text()
binary='/tmp/yulang-source-hir-selective-scc-20261010/debug/deps/yu_solver-12ea9c1c0f03380a'
trace=r'''
import gdb,re,json

def vec(v):
 p=v['buf']['inner']['ptr']['pointer']['pointer'].cast(v.type.template_argument(0).pointer())
 return [p[i] for i in range(int(v['len']))]
def variant(v):
 names=[f.name for f in v.type.fields() if f.name]
 return names[-1],v[names[-1]]
def row(v):
 m=re.search(r'Effect\((\d+)\)',str(v));return int(m.group(1)) if m else None
snapshot_counter=0
def snapshot(s,label,verbose=False):
 global snapshot_counter
 snapshot_counter+=1
 st=s['candidate_graph']['Some']['__0'];al=st['intrusion']['effect_algebra'];views=vec(al['views']);bs=vec(s['effect_bounds']);reps=[int(x) for x in vec(st['intrusion']['effects'])]
 adj={}
 for i,b in enumerate(bs):
  adj[i]=set(int(x) for k in ('direct_lower_rows','direct_upper_rows') for x in vec(b[k]))
  for k in ('exact_non_variable_lowers','exact_non_variable_uppers'):
   for x in vec(b[k]):
    m=re.search(r'(?:Allowance|Support)\((\d+)\)',str(x))
    if m:
     t=views[int(m.group(1))]['tail']
     if 'Some' in str(t):adj[i].add(int(t['Some']['__0']))
 def rep(i):
  while i<len(reps) and reps[i]!=i:i=reps[i]
  return i
 def reach(i):
  found=set();todo=[rep(i)]
  while todo:
   x=rep(todo.pop())
   if x not in found:found.add(x);todo.extend(adj.get(x,()))
  return found
 pairs=[]
 for p in vec(st['intrusion']['parents']):
  c,o=row(p['copy']),row(p['parent'])
  if c is not None:
   cr,pr=rep(c),rep(o);ret=pr in reach(cr)
   pairs.append((c,o,str(p['polarity']),int(p['target']),cr,pr,ret,sorted(reach(cr))))
 qualifying=[p for p in pairs if p[4]!=p[5] and p[6]]
 if verbose or qualifying:
  print('SNAPSHOT',snapshot_counter,label,'ERRORS',int(s['errors']['len']),'GEN',int(st['intrusion']['generation']),'DIRTY',str(st['intrusion']['dirty']))
  print('PAIRS',json.dumps(pairs))
  for i,b in enumerate(bs):
   print('ROW',i,'LEVEL',vec(s['effect_levels'])[i],'REP',rep(i),'DL',[int(x) for x in vec(b['direct_lower_rows'])],'DU',[int(x) for x in vec(b['direct_upper_rows'])],'EL',[str(x) for x in vec(b['exact_non_variable_lowers'])],'EU',[str(x) for x in vec(b['exact_non_variable_uppers'])])
  for i,v in enumerate(views):print('VIEW',i,'TAIL',v['tail'],'POS',v['position'],'OWNER',v['owner'])
 return qualifying
class ActionTrace(gdb.Breakpoint):
 def stop(self):
  a=gdb.parse_and_eval('action').dereference();k,x=variant(a);s=gdb.parse_and_eval('self').dereference();desc=[]
  for f in x.type.fields():
   n=f.name
   if n=='occurrence':desc.append('occ='+str(x[n]['ordinal']))
   elif n in ('slot','level','boundary','value','target','parameter','endpoint','initializer','computation_effect','__0'):desc.append(n+'='+str(x[n]))
  if k=='Fact':
   fact=vec(s['batch']['occurrences'])[int(x['__0'])];desc.append('occ='+str(fact['id']['occurrence']['ordinal'])+'/'+str(fact['id']['local_slot']))
  print('ACTION',k,' '.join(desc));return False
class IncomingTrace(gdb.Breakpoint):
 def stop(self):
  print('INCOMING_OWNER',gdb.parse_and_eval('source'),'TAIL',gdb.parse_and_eval('tail'),'ALLOW',gdb.parse_and_eval('allowance'));return False
class SettleTrace(gdb.Breakpoint):
 def stop(self):
  try:snapshot(gdb.parse_and_eval('self').dereference(),'before-merges')
  except gdb.error as e:print('SNAP_ERROR',str(e))
  return False
class AllowTrace(gdb.Breakpoint):
 def stop(self):
  b=gdb.parse_and_eval('bound')
  if 'Allowance' in str(b):print('REGISTER_ALLOW',b)
  return False
ActionTrace('crates/yu-solver/src/candidate_source.rs:551',internal=True)
IncomingTrace('crates/yu-solver/src/candidate_extrusion.rs:303',internal=True)
SettleTrace('crates/yu-solver/src/candidate_intrusion.rs:493',internal=True)
AllowTrace('crates/yu-solver/src/candidate_effect.rs:427',internal=True)
'''
commands=['set pagination off','set debuginfod enabled off','set print elements 0','break yu_solver::candidate_effect::tests::make_session','run candidate_effect::tests::formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber --exact --test-threads=1','set language c','set $probe = (char*)malloc(8192)','call (void)memcpy($probe, '+json.dumps(source)+', '+str(len(source))+')','set text.data_ptr = (unsigned char*)$probe','set text.length = '+str(len(source)),'set $rdi = $probe','set $rsi = '+str(len(source)),'set language rust','break crates/yu-solver/src/candidate_effect.rs:1879','python exec('+json.dumps(trace)+')','continue','python snapshot(gdb.parse_and_eval("session"),"end-root",True)']
args=['timeout','45s','gdb','-q','-nx','-batch']
for c in commands:args+=['-ex',c]
def limit():
 os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
 resource.setrlimit(resource.RLIMIT_AS,(1536*1024*1024,1536*1024*1024))
 resource.setrlimit(resource.RLIMIT_CPU,(85,85))
start=time.monotonic()
with (base/(sys.argv[1]+'.log')).open('w') as out:
 r=subprocess.run(args+[binary],stdout=out,stderr=subprocess.STDOUT,preexec_fn=limit,timeout=50)
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
print(json.dumps({'variant':sys.argv[1],'returncode':r.returncode,'wall_s':time.monotonic()-start,'maxrss_kib':usage.ru_maxrss,'user_s':usage.ru_utime,'system_s':usage.ru_stime}))
```

## Frozen dependency manifest and commit packet

```text
8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0  crates/yu-solver/src/candidate_source.rs
2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e  crates/yu-solver/src/candidate_effect.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  crates/yu-solver/src/candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  crates/yu-solver/src/candidate_intrusion.rs
582bfb741315534dacf7290bb5618452bb55d9949a8aac691d8d01b93720de11  crates/yu-solver/src/candidate_scheme.rs
3b219b51ed8aba6ffc85675fd1d500b901a6f63b31325a85a586d688eee3515a  crates/yu-solver/src/candidate_context.rs
2635a036a520001ecf6387ee8e1edabcb463e2f1f8d82ab1482797c24bb37f30  crates/yu-solver/src/candidate_context_tests.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  crates/yu-solver/src/lib.rs
6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6  crates/yu-solver/src/shadow_apply.rs
906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed  crates/yu-hir/src/module/local_source.rs
a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb  crates/yu-hir/src/module/source_annotation.rs
a3f39b574e343b2065897e6df3b04ccf525a31df5fea1ed69ecc0bf07611e41a  Cargo.lock
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  notes/design/2026-10-10-contextual-attachment-admission-design.md
15720e628305d76e810506464c4cc684ad101cd3fe79ed12ec7d0c0116205252  notes/progress/2026-10-10-function-port-source-return-search.md
17936a4926135bf04bedb52a2640073227ee17f8f971ba549095b227e56b8e81  notes/progress/2026-10-10-source-hir-selective-scc-witness.md
3376b6d6b05d90653b91d47a66c5ae522b3b2014bccaca3dfa40e5940cd1d7b2  notes/progress/2026-10-10-source-hir-selective-scc-proof.md
6e8a41bc27e0570c916cf49fa4e4a916b6bb6059ad8b0c32627a2d33a0cfbf93  notes/progress/2026-10-10-positive-tail-source-composition-proof.md
7aee4053118d02e626d70695433018c356105e8e7663e3f9776b5d922c4a4ec3  /tmp/yulang-source-hir-selective-scc-20261010/debug/deps/yu_solver-12ea9c1c0f03380a
29a24172567efbdd5acc0a331699ef34fe599244022fa9d167bdd746e9c12f91  /tmp/yulang-positive-port-source-route-20261010/run.py
```

Commit packet: exact changed tracked path
`notes/progress/2026-10-10-positive-port-source-route-search.md`; primary-supplied
baseline `09ea300c3`; no dependency changed by this producer, final source
hashes equal initial inspected values. Review status: frozen, unreviewed,
research-only bounded source characterization; R remains OPEN. Checks already
run: the eight ordinary-source root schedules, final emitted-state reachability,
static constructor/level tracing, provenance and dependency hashing. Proposed
checkpoint message: `research: bound positive-port source return search`.
Shared-record deltas intentionally deferred to the primary/curator: retain the
positive symbolic self-tail exposure, the exact preceding Value-demand level
collapse of the deeper consumer, all-source and selective owner-return as open,
and the unchanged full restoration/replay-rescue obligations. No tasks/index/
theory/authority status promotion. This note is frozen at handoff; all probe
processes have ended and no writes continue.
