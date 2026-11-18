import os,pathlib,hashlib,subprocess
mods=['GeneralRebaseMultiSelection263','GeneralRebaseValidatedDriver263','GeneralRebaseValidatedOutcome263']
cache=pathlib.Path('lean/.lake/cycle263-driver-review')
for p in pathlib.Path('lean/.lake/cycle263-owners').rglob('*.olean'):
 if p.stem in mods:continue
 q=cache/p.relative_to('lean/.lake/cycle263-owners');q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p.resolve())
env={**os.environ,'LEAN_PATH':str(cache)}
for m in mods:
 p=pathlib.Path('lean/Yulang/'+m+'.lean');print(m,hashlib.sha256(p.read_bytes()).hexdigest(),flush=True)
 r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o',str(cache/'Yulang'/f'{m}.olean'),str(p)],env=env)
 print('EXIT',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','notes/verification/cycle263/DriverReviewProbe.lean'],env=env)
print('PROBE EXIT',r.returncode,flush=True);raise SystemExit(r.returncode)
