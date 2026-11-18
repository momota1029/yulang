from pathlib import Path
import subprocess,os,datetime
v=Path('notes/verification/cycle260');cache=Path('lean/.lake/cycle260-final-critical')
assert 'CRITICAL-LAYER-PASS 58' in v.joinpath('final-critical-build.txt').read_text()
# Expose the fresh focused artifacts to independent lake env audit invocations.
for p in cache.rglob('*.olean'):
 q=Path('lean/.lake/build/lib/lean')/p.relative_to(cache);q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists() or q.is_symlink():q.unlink()
 q.symlink_to(p.resolve())
env={**os.environ,'PATH':str(Path('../toolchain244/bin').resolve())+':'+os.environ['PATH']}
for part in ['Complete','Full','Usage','Types','AllTypes','Reach']:
 print('AUDIT',part,datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
 with v.joinpath(part.lower()+'-final.txt').open('w') as log:
  r=subprocess.run(['lake','env','lean','--trust=0','-DwarningAsError=true','Audit/Cycle260'+part+'.lean'],cwd='lean',env=env,stdout=log,stderr=subprocess.STDOUT)
 if r.returncode:print('FAILED',part,flush=True);raise SystemExit(r.returncode)
for probe,logname in [('RequestAddressProbe','request-address-probe.txt'),('DecoderScopeProbe','decoder-scope-probe.txt')]:
 with v.joinpath(logname).open('w') as log:
  r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true',str(v/(probe+'.lean'))],env={**env,'LEAN_PATH':str(cache)},stdout=log,stderr=subprocess.STDOUT)
 assert r.returncode==0
print('ALL-SIX-AND-TWO-PROBES-PASS',datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
