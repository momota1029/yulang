from pathlib import Path
import os,subprocess,time
base=Path('/workspace/scratch/1d0b4aaa3394'); repo=base/'yulang174-public'; logs=base/'cycle174-verification/final'; env=dict(os.environ,LEAN_PATH=str(base/'cycle174-verification/lib')); exe='/tmp/lean137/lean-4.35.0-linux/bin/lean'
for p in sorted((repo/'lean/Audit').glob('Cycle174*.lean')):
 cmd=[exe,'-j1','--trust=0',str(p)]
 print('COMMAND',' '.join(cmd),flush=True)
 r=subprocess.run(cmd,env=env,cwd=repo/'lean',capture_output=True,text=True,timeout=180)
 print(r.stdout,end='',flush=True);print(r.stderr,end='',flush=True);print('EXIT',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
print('ALL_FOCUSED_AUDITS_PASS',flush=True)
