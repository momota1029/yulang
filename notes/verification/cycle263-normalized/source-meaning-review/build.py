from pathlib import Path
import subprocess,os,hashlib,json
root=Path('/tmp/yulang263-normalized-review/lean/Yulang');cache=Path('lean/.lake/cycle263-normalized-review/Yulang');hashes={}
for name in ['UniversalMeaning','UniversalTrace','SourceMeaning']:
 module='GeneralRebase'+name+'263';path='lean/Yulang/'+module+'.lean'
 source=subprocess.check_output(['git','show','640ae837f:'+path]);target=root/(module+'.lean');target.write_bytes(source)
 hashes[path]=hashlib.sha256(source).hexdigest();out=cache/(module+'.olean')
 if out.is_symlink():out.unlink()
 print('FRESH',module,flush=True)
 subprocess.run(['../toolchain244/bin/lean','--root=/tmp/yulang263-normalized-review/lean','--trust=0','-DwarningAsError=true','-o',str(out),str(target)],env={**os.environ,'LEAN_PATH':str(cache.parent)},check=True)
Path('notes/verification/cycle263-normalized/source-meaning-review/source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
print('PASS 3',flush=True)
