import pathlib,subprocess,os,hashlib
mods=['GeneralRebaseSelectedCheck262','GeneralRebaseSelectedSettle262','GeneralRebaseSelectedMeaning262','GeneralRebaseSelectedFailure262','GeneralRebaseSelectedRegression262','GeneralRebaseSelectedUnused262']
env={**os.environ,'LEAN_PATH':'lean/.lake/cycle262-core'}
for m in mods:
 p=pathlib.Path('lean/Yulang/'+m+'.lean');print(m,hashlib.sha256(p.read_bytes()).hexdigest(),flush=True)
 r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o','lean/.lake/cycle262-core/Yulang/'+m+'.olean',str(p)],env=env)
 print('exit',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
with open('notes/verification/cycle262/selected-audit.txt','w') as out:
 r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','lean/Audit/Cycle262Selected.lean'],env=env,stdout=out,stderr=subprocess.STDOUT)
print('AUDIT EXIT',r.returncode,flush=True);raise SystemExit(r.returncode)
