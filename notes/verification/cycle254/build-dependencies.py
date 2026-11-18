from pathlib import Path
import re,subprocess,os,json,hashlib
root=Path('lean'); cache=root/'.lake/cycle247-clean';seen=set();order=[]
def visit(m):
 if m in seen:return
 seen.add(m);p=root/Path(*m.split('.')).with_suffix('.lean')
 if not p.exists() or (cache/Path(*m.split('.')).with_suffix('.olean')).exists():return
 for dep in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):visit(dep)
 order.append(m)
visit('Yulang.GeneralDictionaryDefaultEvidence204Examples')
v=Path('notes/verification/cycle254');v.joinpath('dependency-build-list.txt').write_text('\n'.join(order)+'\n')
print('Missing dependencies:',len(order),flush=True)
for m in order:
 p=root/Path(*m.split('.')).with_suffix('.lean');o=cache/Path(*m.split('.')).with_suffix('.olean');o.parent.mkdir(parents=True,exist_ok=True)
 r=subprocess.run(['../toolchain244/bin/lean','--trust=0','-DwarningAsError=true','-o',str(o),str(p)],env=dict(os.environ,LEAN_PATH=str(cache)),capture_output=True,text=True)
 with v.joinpath('dependency-build.txt').open('a') as f:f.write(m+' exit='+str(r.returncode)+'\n'+r.stdout+r.stderr)
 print(m,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
