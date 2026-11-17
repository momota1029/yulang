from pathlib import Path
import re,subprocess,os,time,concurrent.futures
root=Path('/workspace/scratch/1d0b4aaa3394/yulang244-recovery/lean'); out=root/'.lake/build/lib/lean';out.mkdir(parents=True,exist_ok=True)
lean='/workspace/scratch/1d0b4aaa3394/toolchain244/bin/lean'
targets=['Yulang.PresenceNormalForm']
deps={}
def collect(n):
 p=root/(n.replace('.','/')+'.lean')
 if n in deps or not p.exists():return
 ds=[m for line in p.read_text().splitlines() if line.startswith('import ') for m in line[7:].split() if (root/(m.replace('.','/')+'.lean')).exists()]
 deps[n]=set(ds)
 for d in ds:collect(d)
for n in targets:collect(n)
print('FOCUSED_DEPENDENCY_COUNT',len(deps),flush=True)
if os.environ.get('COUNT_ONLY'):raise SystemExit
if len(deps)>100:raise SystemExit('NOT RUN: dependency closure exceeds focused recovery budget')
while not Path(lean).exists():time.sleep(2)
env=dict(os.environ,LEAN_PATH=str(out)); done={n for n in deps if (out/(n.replace('.','/')+'.olean')).exists()};running={};start=time.time()
def run(n):
 p=n.replace('.','/');(out/p).parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run([lean,'--trust=0','-DwarningAsError=true','-o',str(out/(p+'.olean')),p+'.lean'],cwd=root,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=240)
 return r.returncode,r.stdout
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 while len(done)<len(deps):
  if time.time()-start>1200:raise SystemExit('FOCUSED DEADLINE')
  for n,ds in deps.items():
   if n not in done and n not in running and ds<=done and len(running)<2:running[n]=ex.submit(run,n)
  if not running:raise SystemExit('dependency cycle')
  time.sleep(.3)
  for n,f in list(running.items()):
   if f.done():
    rc,log=f.result();print(n,rc,log,flush=True)
    if rc:raise SystemExit('FOCUSED FAIL '+n)
    done.add(n);del running[n]
print('FOCUSED CACHE RESTORED',len(done),flush=True)
