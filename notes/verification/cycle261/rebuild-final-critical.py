from pathlib import Path
import re,json,subprocess,datetime
v=Path('notes/verification/cycle261');closure=json.loads(v.joinpath('dependency-source-sha256.json').read_text());selected=set()
prior=json.loads(Path('notes/verification/cycle260/dependency-source-sha256.json').read_text())
for p in closure:
 if p.startswith('lean/Yulang/') and p not in prior:selected.add(p)
seen=set();ordered=[]
def visit(p):
 if p in seen:return
 seen.add(p)
 for m in re.findall(r'^import\s+(\S+)',Path(p).read_text(),re.M):
  q='lean/'+m.replace('.','/')+'.lean'
  if q in selected:visit(q)
 ordered.append(p)
for p in sorted(selected):visit(p)
v.joinpath('final-critical-modules.txt').write_text('\n'.join(ordered)+'\n')
cache=Path('lean/.lake/cycle261-final-critical');cache.mkdir(exist_ok=True)
for p in Path('lean/.lake/cycle261-focused').rglob('*.olean'):
 rel=p.relative_to('lean/.lake/cycle261-focused');src='lean/'+str(rel.with_suffix('.lean'))
 if src in selected:continue
 q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p.resolve())
print('Fresh critical-layer modules:',len(ordered),flush=True)
for p in ordered:
 out=cache/Path(p).relative_to('lean').with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 print('BUILD',p,datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
 import os
 result=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o',str(out),p],env={**os.environ,'LEAN_PATH':str(cache)})
 if result.returncode:raise SystemExit(result.returncode)
print('CRITICAL-LAYER-PASS',len(ordered),flush=True)
