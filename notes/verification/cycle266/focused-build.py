from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import re,os,subprocess,sys,hashlib,json
root=Path('lean').resolve(); cache=root/'.lake/build/lib/lean'; nodes={}
def add(m):
    if m in nodes:return
    p=root/(m.replace('.','/')+'.lean')
    d=[x for x in re.findall(r'^\s*(?:public\s+|private\s+)?import\s+([\w.]+)',p.read_text(),re.M) if (root/(x.replace('.','/')+'.lean')).exists()]
    nodes[m]=d
    for x in d:add(x)
for m in sys.argv[1:]:add(m)
print('FOCUSED CLOSURE',len(nodes),flush=True)
def compile(m):
    p=root/(m.replace('.','/')+'.lean'); o=cache/(m.replace('.','/')+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
    cmd=[os.environ.get('LEAN_BIN','lean'),'--trust=0','-DwarningAsError=true','-R',str(root),'-o',str(o),str(p)]
    r=subprocess.run(cmd,cwd=root,env={**os.environ,'LEAN_PATH':str(cache)},capture_output=True,text=True,timeout=150)
    return m,r.returncode,r.stdout+r.stderr
already={m for m in nodes if not (os.getenv('REBUILD_CYCLE266')=='1' and m.endswith('266')) and (cache/(m.replace('.','/')+'.olean')).exists()}; todo=set(nodes)-already; count=0
with ThreadPoolExecutor(max_workers=6) as pool:
    run=set()
    while todo or run:
        ready=[m for m in todo if all(x in already for x in nodes[m])]
        for m in sorted(ready)[:max(0,6-len(run))]:
            todo.remove(m);run.add(pool.submit(compile,m))
        assert run,sorted(todo)[:12]
        done,run=wait(run,return_when=FIRST_COMPLETED)
        for f in done:
            m,code,msg=f.result()
            if code:print('FAIL',m,msg,flush=True);raise SystemExit(code)
            count+=1;already.add(m);print('BUILD',count,m,flush=True)
print('FOCUSED-PASS',count,len(nodes),flush=True)
Path('notes/verification/cycle266/dependency-sha256.json').write_text(json.dumps({m:hashlib.sha256((root/(m.replace('.','/')+'.lean')).read_bytes()).hexdigest() for m in sorted(nodes)},indent=2)+'\n')
