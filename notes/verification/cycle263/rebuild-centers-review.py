import os,pathlib,re,subprocess,hashlib,json
root=pathlib.Path.cwd(); cache=root/'lean/.lake/cycle263-centers-review'; old=root/'lean/.lake/cycle263-owners'; cache.mkdir(exist_ok=True)
for f in old.rglob('*.olean'):
 p=cache/f.relative_to(old);p.parent.mkdir(parents=True,exist_ok=True)
 if not p.exists():p.symlink_to(f.resolve())
fresh={'Yulang.GeneralRebaseHeadSupport263','Yulang.GeneralRebaseRegisteredPlan263','Yulang.GeneralRebaseRegisteredSites263','Yulang.GeneralRebaseSourceCenters263'}
for n in fresh:
 p=cache/(n.replace('.','/')+'.olean')
 if p.exists():p.unlink()
seen=set();hashes={}
def build(n):
 if n in seen:return
 seen.add(n)
 source=root/'lean'/(n.replace('.','/')+'.lean')
 if not source.exists():return
 hashes[str(source.relative_to(root))]=hashlib.sha256(source.read_bytes()).hexdigest()
 for line in source.read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:build(dep)
 target=cache/(n.replace('.','/')+'.olean')
 if not target.exists():
  print('BUILD',n,flush=True); target.parent.mkdir(parents=True,exist_ok=True)
  subprocess.run([str(root.parent/'toolchain244/bin/lean'),'--trust=0','-DwarningAsError=true','-o',str(target),str(source)],env={**os.environ,'LEAN_PATH':str(cache)},check=True)
  print('PASS',n,flush=True)
build('Yulang.GeneralRebaseSourceCenters263')
(root/'notes/verification/cycle263/centers-review-source-hashes.json').write_text(json.dumps(hashes,indent=2,sort_keys=True)+'\n')
