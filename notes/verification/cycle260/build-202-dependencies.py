from pathlib import Path
import re,subprocess,os
cache=Path('lean/.lake/cycle260-focused');seen=set();built=[]
def visit(m):
 out=cache/Path(*m.split('.')).with_suffix('.olean')
 if out.exists() or m in seen:return
 seen.add(m);src=Path('lean')/Path(*m.split('.')).with_suffix('.lean')
 if not src.exists():return
 for dep in re.findall(r'^import\s+(\S+)',src.read_text(),re.M):visit(dep)
 out.parent.mkdir(parents=True,exist_ok=True)
 print('BUILD',m,flush=True)
 r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o',str(out),str(src)],env={**os.environ,'LEAN_PATH':str(cache)})
 if r.returncode:raise SystemExit(r.returncode)
 built.append(m)
visit('Yulang.GeneralDictionaryVersionedDefault202Local233')
print('MISSING-DEPS-PASS',len(built),flush=True)
