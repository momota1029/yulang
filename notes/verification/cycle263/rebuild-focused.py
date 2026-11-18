from pathlib import Path
import re,json,hashlib,os,subprocess,datetime
v=Path('notes/verification/cycle263'); modules=v.joinpath('modules.txt').read_text().splitlines(); ordered=[];seen=set()
def visit(p):
 if p in seen:return
 seen.add(p)
 assert Path(p).exists(),p
 for m in re.findall(r'^import\s+(\S+)',Path(p).read_text(),re.M):
  if m.startswith('Yulang.') or m in ['Yulang']:visit('lean/'+m.replace('.','/')+'.lean')
 ordered.append(p)
for m in modules:visit('lean/Yulang/'+m+'.lean')
for p in sorted(Path('lean/Audit').glob('Cycle263*.lean')):visit(str(p))
hashes={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in ordered if p.startswith('lean/Yulang/')}
prior=json.loads(Path('notes/verification/cycle262/dependency-source-sha256.json').read_text())
selected=[p for p in ordered if p in hashes and prior.get(p)!=hashes[p]]
old_changed=[p for p in selected if p in prior]
assert not old_changed,('frozen dependency changed',old_changed)
v.joinpath('dependency-source-sha256.json').write_text(json.dumps(hashes,indent=2)+'\n')
v.joinpath('fresh-modules.txt').write_text('\n'.join(selected)+'\n')
cache=Path('lean/.lake/cycle263-final');cache.mkdir(exist_ok=True)
for p in Path('lean/.lake/cycle263-core').rglob('*.olean'):
 rel=p.relative_to('lean/.lake/cycle263-core');src='lean/'+str(rel.with_suffix('.lean'))
 if src in selected:continue
 q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p.resolve())
for p in selected:
 out=cache/Path(p).relative_to('lean').with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 print('BUILD',p,datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
 r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o',str(out),p],env={**os.environ,'LEAN_PATH':str(cache)})
 if r.returncode:raise SystemExit(r.returncode)
print('FRESH-PASS',len(selected),'DEPENDENCY-SOURCES',len(hashes),flush=True)
