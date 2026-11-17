from pathlib import Path
import subprocess,os,json,hashlib
root=Path.cwd(); lean=root.parent/'toolchain244/bin/lean';cache=root/'lean/.lake/build/lib/lean'
env=dict(os.environ,LEAN_PATH=str(cache));mods={m:Path('lean/Yulang')/(m+'.lean') for m in ['GeneralPresenceGuardedAbsorption247', 'GeneralPresenceGuardedAllocation247', 'GeneralPresenceGuardedCommutation247', 'GeneralPresenceGuardedCompression247', 'GeneralPresenceGuardedConsumers247', 'GeneralPresenceGuardedEnvironment247', 'GeneralPresenceGuardedExamples247', 'GeneralPresenceGuardedRebase247', 'GeneralPresenceGuardedRebaseExample247', 'GeneralPresenceGuardedRecovery247', 'GeneralPresenceOrderedAllocation247', 'GeneralPresenceOrderedBlock247', 'GeneralPresenceOrderedCheck247', 'GeneralPresenceOrderedCoherentAdapter247', 'GeneralPresenceOrderedCycleLimit247', 'GeneralPresenceOrderedDedup247', 'GeneralPresenceOrderedDependence247', 'GeneralPresenceOrderedPrepared247', 'GeneralPresenceOrderedQueries247', 'GeneralPresenceOrderedQueryLimit247', 'GeneralPresenceOrderedRebase247', 'GeneralPresenceOrderedRebaseExample247', 'GeneralPresenceOrderedRecovery247', 'GeneralPresenceOrderedRefreshSequence247', 'GeneralPresenceOrderedRefreshSyntax247', 'GeneralPresenceOrderedRewriteAbsorption247', 'GeneralPresenceOrderedSort247', 'GeneralPresenceOrderedSubstitution247', 'GeneralPresenceOrderedSupport247', 'GeneralPresenceOrderedSyntax247']};done=set();order=[]
def visit(n):
 if n in done:return
 done.add(n)
 for line in mods[n].read_text().splitlines():
  if line.startswith('import Yulang.'):
   d=line.split()[1].split('.')[-1]
   if d in mods:visit(d)
 order.append(n)
for n in sorted(mods):visit(n)
print(subprocess.check_output([str(lean),'--version'],text=True).strip(),flush=True)
for n in order:
 r=subprocess.run([str(lean),'--trust=0','-DwarningAsError=true','-o',str(cache/'Yulang'/(n+'.olean')),str(mods[n])],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 print((n+' EXIT '+str(r.returncode)+' '+r.stdout).rstrip(),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
r=subprocess.run([str(lean),'--trust=0','-DwarningAsError=true','lean/Audit/Cycle247Final.lean'],env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
print('AUDIT EXIT',r.returncode,r.stdout,flush=True)
if r.returncode:raise SystemExit(r.returncode)
manifest={str(mods[n]):hashlib.sha256(mods[n].read_bytes()).hexdigest() for n in order}
Path('notes/verification/cycle247/final-source-sha256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('VERIFIED_MODULES',len(order),flush=True)
