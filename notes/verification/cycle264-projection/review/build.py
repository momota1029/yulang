from pathlib import Path
import subprocess,os,hashlib,json
cache=Path('lean/.lake/cycle264-projection-review');deps=Path('lean/.lake/cycle264-projection').resolve();root=Path('/tmp/cycle264-projection-review')
for source in deps.rglob('*.olean'):
 target=cache/source.relative_to(deps);target.parent.mkdir(parents=True,exist_ok=True)
 if not target.exists():target.symlink_to(source)
hashes={}
for name in ['GeneralRebaseLiveMeaning264','GeneralRebaseSourceProjection264']:
 source=Path('/tmp/'+name+'.lean').read_bytes();target=root/'Yulang'/(name+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source)
 hashes[name]=hashlib.sha256(source).hexdigest();out=cache/'Yulang'/(name+'.olean')
 if out.is_symlink():out.unlink()
 subprocess.run(['../toolchain244/bin/lean','--root='+str(root),'--trust=0','-DwarningAsError=true','-o',str(out),str(target)],env={**os.environ,'LEAN_PATH':str(cache)},check=True)
 print('PASS',name,flush=True)
Path('notes/verification/cycle264-projection/review/source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
