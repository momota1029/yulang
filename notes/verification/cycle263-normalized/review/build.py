from pathlib import Path
import subprocess,os,re,hashlib,json
revision='755fc5a8d'
root=Path('/tmp/yulang263-normalized-review');cache=Path('lean/.lake/cycle263-normalized-review');root.mkdir(exist_ok=True);cache.mkdir(parents=True,exist_ok=True)
deps=Path('lean/.lake/cycle263-normalized').resolve()
for source in deps.rglob('*.olean'):
 target=cache/source.relative_to(deps);target.parent.mkdir(parents=True,exist_ok=True)
 if not target.exists():target.symlink_to(source)
seen=set();hashes={}
def build(name):
 if name in seen:return
 seen.add(name)
 path='lean/'+name.replace('.','/')+'.lean'
 source=subprocess.run(['git','show',revision+':'+path],capture_output=True,text=True)
 if source.returncode:raise Exception(path)
 if not name.endswith('263') or 'Normalized' in name or 'HeadSupport' in name:return
 for dep in re.findall(r'^import\s+(\S+)',source.stdout,re.M):build(dep)
 target=root/Path(path);target.parent.mkdir(parents=True,exist_ok=True);target.write_text(source.stdout)
 hashes[path]=hashlib.sha256(source.stdout.encode()).hexdigest()
 out=cache/Path(name.replace('.','/')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 if out.is_symlink():out.unlink()
 print('FRESH',name,flush=True)
 subprocess.run(['../toolchain244/bin/lean','--root='+str(root/'lean'),'--trust=0','-DwarningAsError=true','-o',str(out),str(target)],env={**os.environ,'LEAN_PATH':str(cache)+':'+str(deps)},check=True)
for name in ['MultiObserver','MultiRun','MultiTrace','MultiSource']:build('Yulang.GeneralRebase'+name+'263')
Path('notes/verification/cycle263-normalized/review/source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print('PASS',len(hashes),flush=True)
