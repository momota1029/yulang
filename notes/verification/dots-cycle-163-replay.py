import subprocess,pathlib,re,os,sys,hashlib,json
# Usage: python replay.py REPO COMMIT LEAN_BINARY CACHE_DIR
repo=pathlib.Path(sys.argv[1]).resolve();commit=sys.argv[2];dest=repo.parent/'y163-published-source';dest.mkdir(exist_ok=True)
def source(p):return subprocess.check_output(['git','show',commit+':'+p],cwd=repo)
items=json.loads(source('notes/verification/dots-cycle-163-inventory.json'));mods={}
for i in items:
 data=source(i['path']);assert hashlib.sha256(data).hexdigest()==i['sha256'],i['path'];p=dest/i['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);mods[i['namespace']]=p
print('PUBLIC SOURCE SHA256 MATCH',len(items),flush=True)
lib=pathlib.Path(sys.argv[4]).resolve();env=dict(os.environ,LEAN_PATH=str(lib));lean=sys.argv[3];done=set()
def build(m):
 if m in done:return
 p=mods[m]
 for dep in re.findall(r'^import (\S+)',p.read_text(),re.M):
  if dep in mods:build(dep)
 out=lib/(m.replace('.','/')+'.olean')
 if out.is_symlink():out.unlink()
 r=subprocess.run([lean,'--trust=0','-o',str(out),str(p)],cwd=dest/'lean',env=env,capture_output=True,text=True,timeout=180)
 print(m,r.returncode,r.stdout,r.stderr,flush=True)
 if r.returncode:raise SystemExit(1)
 done.add(m)
for m in mods:build(m)
gate=dest/'Cycle163FinalDependencyGate.lean';gate.write_bytes(source('lean/Audit/Cycle163FinalDependencyGate.lean'))
r=subprocess.run([lean,'--trust=0',str(gate)],cwd=dest/'lean',env=env,capture_output=True,text=True,timeout=180);print('PUBLISHED GATE',r.returncode,r.stdout,r.stderr,flush=True);raise SystemExit(r.returncode)
