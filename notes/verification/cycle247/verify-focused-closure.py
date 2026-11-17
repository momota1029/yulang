from pathlib import Path
import subprocess,os,json,time,hashlib
root=Path.cwd();lean=root.parent/'toolchain244/bin/lean';cache=root/'lean/.lake/cycle247-clean';cache.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_PATH=str(cache));order=json.loads(Path('notes/verification/cycle247/focused-closure.json').read_text());start=time.monotonic();hashes={}
for module in order:
 source=root/'lean'/(module.replace('.','/')+'.lean');out=cache/(module.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 result=subprocess.run([str(lean),'--trust=0','-DwarningAsError=true','-o',str(out),str(source)],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=120)
 print((module+' EXIT '+str(result.returncode)+' '+result.stdout).rstrip(),flush=True)
 if result.returncode:raise SystemExit(result.returncode)
 hashes[str(source.relative_to(root))]=hashlib.sha256(source.read_bytes()).hexdigest()
Path('notes/verification/cycle247/focused-closure-sha256.json').write_text(json.dumps(hashes,indent=2)+'\n')
print('FOCUSED_CLEAN_CLOSURE_PASS',len(order),'SECONDS',round(time.monotonic()-start,2),flush=True)
