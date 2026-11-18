from pathlib import Path
import re,subprocess,os,datetime
cache=Path('lean/.lake/cycle261-focused');seen=set();ordered=[]
def visit(m):
 p=Path('lean')/Path(*m.split('.')).with_suffix('.lean');o=cache/Path(*m.split('.')).with_suffix('.olean')
 if m in seen or o.exists():return
 seen.add(m)
 if not p.exists():raise RuntimeError(str(p))
 for q in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(q)
 ordered.append((p,o))
visit('Yulang.GeneralNominalCenteredHeadAllocV7MergeRegression')
print('Missing focused dependencies',len(ordered),flush=True)
for p,o in ordered:
 print('BUILD',p,datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True);o.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o',str(o),str(p)],env={**os.environ,'LEAN_PATH':str(cache)})
 if r.returncode:raise SystemExit(r.returncode)
print('DEPENDENCY-PASS',len(ordered),flush=True)
