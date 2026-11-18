from pathlib import Path
import subprocess,os,re,hashlib,json
cache=Path('lean/.lake/cycle263-normalized');seen=set();built=[];manifest={}
mods=['GeneralRebaseNormalizedBody263','GeneralRebaseNormalizedFacts263','GeneralRebaseHeadSupport263','GeneralRebaseNormalizedExamples263','GeneralRebaseRegisteredPlan263','GeneralRebaseRegisteredSites263','GeneralRebaseSourceCenters263']
def visit(module):
 if module in seen:return
 seen.add(module);p=Path('lean')/Path(module.replace('.','/')).with_suffix('.lean')
 if not p.exists():return
 manifest[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
 for dep in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(dep)
 out=cache/Path(module.replace('.','/')).with_suffix('.olean')
 if out.exists() and not module.endswith('263') and not module.endswith(('GeneralDictionaryDefault214ActualShadowRegression','GeneralNominalVersionedCurrentProjection237')):return
 print('BUILD',p,flush=True);out.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o',str(out),str(p)],env={**os.environ,'LEAN_PATH':str(cache)})
 if r.returncode:raise SystemExit(r.returncode)
 built.append(module)
for m in mods:visit('Yulang.'+m)
Path('notes/verification/cycle263-normalized/source-hashes.json').write_text(json.dumps(manifest,indent=2)+'\n')
Path('notes/verification/cycle263-normalized/fresh-modules.json').write_text(json.dumps(built,indent=2)+'\n')
print('PASS',len(built),flush=True)
