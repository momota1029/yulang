from pathlib import Path
import subprocess,os,datetime
v=Path('notes/verification/cycle263'); cache=Path('lean/.lake/cycle263-final'); assert 'FRESH-PASS' in v.joinpath('fresh-build.txt').read_text()
for p in cache.rglob('*.olean'):
 q=Path('lean/.lake/build/lib/lean')/p.relative_to(cache); q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists() or q.is_symlink():q.unlink()
 q.symlink_to(p.resolve())
env={**os.environ,'PATH':str(Path('../toolchain244/bin').resolve())+':'+os.environ['PATH']}
for part in [p.stem.removeprefix('Cycle263') for p in sorted(Path('lean/Audit').glob('Cycle263*.lean'))]:
 print('AUDIT',part,datetime.datetime.now(datetime.timezone.utc).isoformat(),flush=True)
 with v.joinpath(part.lower()+'-final.txt').open('w') as log:
  r=subprocess.run(['lake','env','lean','--trust=0','-DwarningAsError=true','Audit/Cycle263'+part+'.lean'],cwd='lean',env=env,stdout=log,stderr=subprocess.STDOUT)
 if r.returncode:raise SystemExit(r.returncode)
print('STANDALONE-AUDITS-PASS',flush=True)
