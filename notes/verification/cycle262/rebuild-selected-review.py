from pathlib import Path
import hashlib,json,subprocess,os,datetime,re
v=Path('notes/verification/cycle262');old=Path('lean/.lake/cycle262-core');new=Path('lean/.lake/cycle262-selected-review')
mods=['GeneralRebaseSelectedCheck262','GeneralRebaseSelectedSettle262','GeneralRebaseSelectedMeaning262','GeneralRebaseSelectedRegression262','GeneralRebaseQuadraticBudget262']
hashes={str(Path('lean/Yulang')/(m+'.lean')):hashlib.sha256((Path('lean/Yulang')/(m+'.lean')).read_bytes()).hexdigest() for m in mods}
v.joinpath('selected-review-source-sha256.json').write_text(json.dumps(hashes,indent=2)+'\n')
for p in old.rglob('*.olean'):
 if p.stem in mods:continue
 q=new/p.relative_to(old);q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p.resolve())
env={**os.environ,'LEAN_PATH':str(new)}
for m in mods:
 cmd=['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o',str(new/'Yulang'/(m+'.olean')),'lean/Yulang/'+m+'.lean']
 print('BUILD',datetime.datetime.now(datetime.timezone.utc).isoformat(),' '.join(cmd),flush=True)
 r=subprocess.run(cmd,env=env)
 print('EXIT',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
probe=''.join('import Yulang.'+m+'\n' for m in mods)
count=0
for m in mods:
 for n in re.findall(r'^(?:theorem|def|abbrev|inductive|structure)\s+([A-Za-z0-9_]+)',Path('lean/Yulang/'+m+'.lean').read_text(),re.M):
  probe+='#print axioms Yulang.'+m+'.'+n+'\n';count+=1
probe+='#check @Yulang.GeneralRebaseSelectedMeaning262.source_certificate\n#check @Yulang.GeneralRebaseQuadraticBudget262.run_bound\n'
v.joinpath('SelectedReviewProbe.lean').write_text(probe)
cmd=['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true',str(v/'SelectedReviewProbe.lean')]
with v.joinpath('selected-independent-audit.txt').open('w') as log:r=subprocess.run(cmd,env=env,stdout=log,stderr=subprocess.STDOUT)
print('AUDIT EXIT',r.returncode,'DECLARATIONS',count,flush=True)
assert r.returncode==0
assert all(hashlib.sha256(Path(p).read_bytes()).hexdigest()==sha for p,sha in hashes.items())
print('FRESH-FIVE-MODULE-AUDIT-PASS; SOURCE-HASHES-UNCHANGED',flush=True)
