from pathlib import Path
import os,sys,subprocess,time,json,resource,re,hashlib,signal
root=Path('/home/momota1029/rust/yulang')
scratch=root/'isolated/ep-annotated-relay-r21/lean-scratch'
module='YulangClosure.FormalPermissionAnnotatedRelay'
source=root/'notes/theory/lean/YulangClosure/FormalPermissionAnnotatedRelay.lean'
names=re.findall(r'^theorem ([A-Za-z_][A-Za-z0-9_]*)',source.read_text(),re.M)
seconds=float(sys.argv[1]); run=sys.argv[2]
args=['python3',str(root/'.agents/skills/yulang-lean-proofs/scripts/check_lean.py'),'--project',str(scratch/'project'),'--lake','/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lake','--timeout',str(seconds),'--module',module]
for name in names: args+=['--theorem',module+'.'+name]
env=dict(os.environ,TMPDIR=str(scratch/'tmp'),LEAN_NUM_THREADS='1')
def limits():
 if hasattr(os,'sched_getaffinity'):
  os.sched_setaffinity(0,{min(os.sched_getaffinity(0))})
start=time.monotonic()
with (scratch/f'audit-{run}.log').open('w') as out:
 p=subprocess.Popen(args,stdout=out,stderr=subprocess.STDOUT,env=env,preexec_fn=limits,start_new_session=True)
 peak=0
 stop_reason=None
 while p.poll() is None:
  processes={}
  for stat in Path('/proc').glob('[0-9]*/stat'):
   try:
    data=stat.read_text().rsplit(')',1)[1].split()
    processes[int(stat.parent.name)]=(int(data[1]),int(data[21])*os.sysconf('SC_PAGE_SIZE'))
   except (OSError,ValueError,IndexError): pass
  live={p.pid}
  changed=True
  while changed:
   old=len(live)
   live.update(pid for pid,(parent,rss) in processes.items() if parent in live)
   changed=len(live)!=old
  current=sum(processes.get(pid,(0,0))[1] for pid in live)
  peak=max(peak,current)
  if current>1024**3 or time.monotonic()-start>seconds+3:
   stop_reason='RSS limit' if current>1024**3 else 'outer timeout'
   os.killpg(p.pid,signal.SIGKILL)
   break
  time.sleep(0.02)
 p.wait()
elapsed=time.monotonic()-start
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
result={'argv':args,'exit':p.returncode,'wall_seconds':elapsed,'max_rss_kib':usage.ru_maxrss,'rss_limit_bytes':1024**3,'sampled_tree_peak_rss_bytes':peak,'stop_reason':stop_reason,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'theorems':names,'TMPDIR':str(scratch/'tmp'),'cpu_affinity_count':1}
(scratch/f'audit-{run}.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
print((scratch/f'audit-{run}.log').read_text())
sys.exit(p.returncode)
