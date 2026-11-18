import pathlib,subprocess,os,json,hashlib
root=pathlib.Path.cwd();cache=root/'lean/.lake/cycle264-current';seen=set();built=[];hashes={}
def build(n):
 if n in seen:return
 seen.add(n);src=root/'lean'/(n.replace('.','/')+'.lean')
 if not src.exists():return
 hashes[str(src.relative_to(root))]=hashlib.sha256(src.read_bytes()).hexdigest()
 for line in src.read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:build(dep)
 out=cache/(n.replace('.','/')+'.olean')
 if not out.exists() or n.endswith('264'):
  if out.is_symlink():out.unlink()
  print('BUILD',n,flush=True)
  subprocess.run([str(root.parent/'toolchain244/bin/lean'),'--trust=0','-DwarningAsError=true','-o',str(out),str(src)],env={**os.environ,'LEAN_PATH':str(cache)},check=True)
  built.append(n);print('PASS',n,flush=True)
import sys
for n in sys.argv[1:]:build(n)
(root/'notes/verification/cycle264-current/source-hashes.json').write_text(json.dumps(hashes,indent=2)+'\n')
