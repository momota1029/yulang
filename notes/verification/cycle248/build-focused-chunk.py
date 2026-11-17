from pathlib import Path
import subprocess,os,json,hashlib,time,fcntl
root=Path.cwd();cache=root/'lean/.lake/cycle247-clean';lean=root.parent/'toolchain244/bin/lean';folder=root/'notes/verification/cycle248'
lock=open(folder/'builder.lock','w');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
target=os.environ.get('TARGET','Yulang.GeneralNominalRebaseOriginView243');seconds=int(os.environ.get('CHUNK_SECONDS','120'))
manifestPath=folder/'dependency-source-sha256.json'
manifest=json.loads(manifestPath.read_text()) if manifestPath.exists() else json.loads((root/'notes/verification/cycle247/clean-final-source-sha256.json').read_text())
seen=set();order=[]
def visit(module):
 if module in seen:return
 seen.add(module);source=root/'lean'/(module.replace('.','/')+'.lean')
 if source.exists():
  for line in source.read_text().splitlines():
   if line.startswith('import '):
    for dep in line.split()[1:]:
     if (root/'lean'/(dep.replace('.','/')+'.lean')).exists():visit(dep)
  order.append(module)

for chosen in target.split(','):visit(chosen)
(folder/'dependency-order.json').write_text(json.dumps(order,indent=2)+'\n')
env=dict(os.environ,LEAN_PATH=str(cache));start=time.monotonic();built=0;remaining=0
for module in order:
 source=root/'lean'/(module.replace('.','/')+'.lean');key=str(source.relative_to(root));sha=hashlib.sha256(source.read_bytes()).hexdigest();output=cache/(module.replace('.','/')+'.olean')
 if output.exists() and manifest.get(key)==sha:continue
 remaining+=1
 if time.monotonic()-start>=seconds:continue
 output.parent.mkdir(parents=True,exist_ok=True)
 tick=time.monotonic()
 try:r=subprocess.run([str(lean),'--trust=0','-DwarningAsError=true','-o',str(output),str(source)],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=90)
 except subprocess.TimeoutExpired:print('TIMEOUT',module,flush=True);raise SystemExit(124)
 print((module+' EXIT '+str(r.returncode)+' SECONDS '+str(round(time.monotonic()-tick,2))+' '+r.stdout).rstrip(),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 manifest[key]=sha;manifestPath.write_text(json.dumps(manifest,indent=2)+'\n');built+=1
print('CHUNK_DONE','TARGET',target,'BUILT',built,'REMAINING',remaining-built,'SECONDS',round(time.monotonic()-start,2),flush=True)
