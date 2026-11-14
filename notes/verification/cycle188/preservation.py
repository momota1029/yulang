import subprocess
from pathlib import Path
base='17f41b7fbedd15a32797781c8a3f94b270740dd8'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',base]).decode().splitlines()
for p in paths:
    if p=='notes/heartbeat/dots-main.md': continue
    old=subprocess.check_output(['git','show',base+':'+p])
    now=Path(p).read_bytes()
    if p=='lean/Yulang.lean': assert now.startswith(old),p
    else: assert now==old,p
print('PRESERVATION-PASS',len(paths),'old paths; root append-only, heartbeat replaced')
