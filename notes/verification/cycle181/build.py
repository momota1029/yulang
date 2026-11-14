from pathlib import Path
import re,subprocess,os,sys
base=Path('/workspace/scratch/1d0b4aaa3394');root=base/'yulang181-public';old=base/'yulang180-public';lib=base/'cycle181-verification/lib';lib.mkdir(exist_ok=True)
if not (lib/'Yulang').exists():subprocess.run(['cp','-as',str(base/'cycle180-verification/lib')+'/.',str(lib)],check=True)
roots=sys.argv[1:] or ['Yulang.GeneralNominalActualBoundary','Yulang.GeneralNominalActualPhaseBoundary']
seen=set();order=[];changed=set()
def visit(n):
 if n in seen:return
 seen.add(n);p=root/'lean'/(n.replace('.','/')+'.lean')
 if not p.exists():return
 for d in re.findall(r'^import (\S+)',p.read_text(),re.M):visit(d)
 q=old/'lean'/(n.replace('.','/')+'.lean')
 # cache172 sources for previous172 modules

 if not q.exists() or p.read_bytes()!=q.read_bytes() or not (lib/(n.replace('.','/')+'.olean')).exists():changed.add(n)
 if n in changed or any(d in changed for d in re.findall(r'^import (\S+)',p.read_text(),re.M)):changed.add(n);order.append(n)
for n in roots:visit(n)
print('DEPENDENCY_CLOSURE',len(seen),'REBUILD',len(order),flush=True)
(base/'cycle181-verification/build-order.txt').write_text('\n'.join(order))
exe='/tmp/lean137/lean-4.35.0-linux/bin/lean'; env=dict(os.environ,LEAN_PATH=str(lib))
for n in order:
 p=root/'lean'/(n.replace('.','/')+'.lean');out=lib/(n.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 if out.is_symlink():out.unlink()
 print('START',n,flush=True)
 try:r=subprocess.run([exe,'-j1','--trust=0','-DwarningAsError=true','-o',str(out),str(p)],cwd=root/'lean',env=env,timeout=180)
 except subprocess.TimeoutExpired:print('TIMEOUT',n,flush=True);sys.exit(124)
 print('END',n,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
print('PASS',len(order),flush=True)
