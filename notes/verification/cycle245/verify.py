from pathlib import Path
import subprocess,os,json,hashlib
root=Path.cwd(); lean=root.parent/'toolchain244/bin/lean';cache=root/'lean/.lake/build/lib/lean'
env=dict(os.environ,LEAN_PATH=str(cache));mods={p.stem:p for p in Path('lean/Yulang').glob('*245.lean')};done=set();order=[]
def visit(n):
 if n in done:return
 done.add(n)
 for line in mods[n].read_text().splitlines():
  if line.startswith('import Yulang.'):
   d=line.split()[1].split('.')[-1]
   if d in mods:visit(d)
 order.append(n)
for n in sorted(mods):visit(n)
print(subprocess.check_output([str(lean),'--version'],text=True).strip(),flush=True)
for n in order:
 r=subprocess.run([str(lean),'--trust=0','-DwarningAsError=true','-o',str(cache/'Yulang'/(n+'.olean')),str(mods[n])],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print(n,'EXIT',r.returncode,r.stdout,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
r=subprocess.run([str(lean),'--trust=0','-DwarningAsError=true','lean/Audit/Cycle245Observed.lean'],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
print('AUDIT EXIT',r.returncode,r.stdout,flush=True)
if r.returncode:raise SystemExit(r.returncode)
manifest={str(mods[n]):hashlib.sha256(mods[n].read_bytes()).hexdigest() for n in order}
Path('notes/verification/cycle245/source-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('VERIFIED_MODULES',len(order),flush=True)
